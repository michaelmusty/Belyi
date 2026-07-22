/* makek_relfinder.c -- batched, certified algebraic-number recognition for
 * the MakeK stage of BelyiMap (FLINT >= 3.0: fmpz_lll + fmpz_poly_factor +
 * arb/acb).
 *
 * The Magma-side recognition loop (genuszero.m / theta.m MakeK) walks
 * candidate degrees m = passportsize..1 over ~50 numerical coefficients,
 * calling PowerRelation once per (coefficient, degree) pair.  Each call is
 * minutes of Magma-side exact LLL, the loop is O(m * #coeffs) calls, and --
 * crucially -- when the working precision cannot certify any relation the
 * loop grinds to the very end before failing (observed: an M24 genus-0 run
 * spent 15+ CPU-hours in 134 doomed MakeK calls at prec 400 before being
 * killed).
 *
 * This tool replaces that loop with ONE pass: for each candidate coefficient
 * u it runs a single integer-relation LLL at the passport degree bound,
 * factors the resulting relation over Z, and certifies which irreducible
 * factor actually vanishes at u (arb evaluation at full precision).  The
 * true minimal polynomial (any degree <= bound) falls out directly; if
 * nothing certifies, the candidate is reported NOPREC, so the caller can
 * abort with "insufficient precision" in seconds instead of days.
 *
 * Input (text file, decimal reals as printed by Magma):
 *   line 1:  prec_bits  ncand  maxm
 *   then per candidate, two lines: Re(u) and Im(u) as decimal strings.
 * Output (text file, machine-parseable, no eval needed on the Magma side):
 *   per candidate one line:
 *     FOUND <index> <degree> <log10resid> <c_0> ... <c_degree>
 *   or
 *     NOPREC <index>
 *   terminated by a line "RELFINDER_DONE <nfound>".
 *
 * Threads: MAKEK_RELFINDER_THREADS (default 1) over candidates.
 * Selftest: ./makek_relfinder --selftest
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <pthread.h>
#include <math.h>

#include <flint/fmpz.h>
#include <flint/fmpz_vec.h>
#include <flint/fmpz_mat.h>
#include <flint/fmpz_lll.h>
#include <flint/fmpz_poly.h>
#include <flint/fmpz_poly_factor.h>
#include <flint/arb.h>
#include <flint/acb.h>
#include <flint/arf.h>

typedef struct {
    slong idx;
    acb_t u;            /* the complex number to recognize */
    int status;         /* 0 = pending, 1 = found, -1 = noprec */
    fmpz_poly_t minpoly;
    double log10resid;
} cand_t;

/* log2 of the L2 norm of a matrix row (via bit length of the sum of
 * squares); used for the LLL gap test */
static double
row_log2norm(const fmpz_mat_t M, slong row, slong ncols)
{
    fmpz_t ss, sq;
    double out;
    fmpz_init(ss);
    fmpz_init(sq);
    for (slong j = 0; j < ncols; j++)
    {
        fmpz_mul(sq, fmpz_mat_entry(M, row, j), fmpz_mat_entry(M, row, j));
        fmpz_add(ss, ss, sq);
    }
    out = fmpz_is_zero(ss) ? -1e9 : 0.5 * (double) fmpz_bits(ss);
    fmpz_clear(ss);
    fmpz_clear(sq);
    return out;
}

/* Block gap test.  A reduced relation lattice splits into a block of short
 * rows (the true relation and, in the minpoly mode with bound > degree, its
 * x^k multiples) and a block of junk rows at the lattice noise scale.  Sort
 * the row norms, find the largest jump between consecutive norms, and
 * return that jump (in bits) if the candidate row lies in the lower block
 * -- else 0.  Junk-only bases have no significant jump. */
static double
lll_gap_bits(const fmpz_mat_t M, slong row, slong nrows, slong ncols)
{
    double *norms = malloc(nrows * sizeof(double));
    double mine = row_log2norm(M, row, ncols);
    slong nn = 0;
    for (slong r = 0; r < nrows; r++)
    {
        double nr = row_log2norm(M, r, ncols);
        if (nr > -1e8)
            norms[nn++] = nr;
    }
    if (nn < 2) { free(norms); return 0.0; }
    /* insertion sort (nn is tiny) */
    for (slong i = 1; i < nn; i++)
    {
        double v = norms[i];
        slong j = i - 1;
        while (j >= 0 && norms[j] > v) { norms[j + 1] = norms[j]; j--; }
        norms[j + 1] = v;
    }
    double best_jump = 0.0, blocktop = norms[0];
    for (slong i = 0; i + 1 < nn; i++)
    {
        double jump = norms[i + 1] - norms[i];
        if (jump > best_jump) { best_jump = jump; blocktop = norms[i]; }
    }
    double out = (mine <= blocktop + 1e-9) ? best_jump : 0.0;
    free(norms);
    return out;
}

#define GAP_CERT_BITS 40.0
#define GAP_UNCERT_BITS 10.0

typedef struct {
    cand_t *cands;
    slong ncand;
    slong maxm;
    slong prec;
    slong next;         /* work queue cursor */
    pthread_mutex_t mtx;
} work_t;

/* certified |p(u)| in arb; returns log10 of an upper bound on |p(u)|, and
 * writes the midpoint magnitude for reporting */
static double
poly_eval_log10(const fmpz_poly_t p, const acb_t u, slong prec)
{
    acb_t val;
    arb_t abs;
    double out;
    acb_init(val);
    arb_init(abs);
    /* Horner with fmpz coefficients */
    acb_zero(val);
    for (slong i = fmpz_poly_degree(p); i >= 0; i--)
    {
        acb_mul(val, val, u, prec);
        acb_add_fmpz(val, val, fmpz_poly_get_coeff_ptr((fmpz_poly_struct *) p, i), prec);
    }
    acb_abs(abs, val, prec);
    /* upper bound of the ball */
    {
        arf_t ub;
        arf_init(ub);
        arb_get_ubound_arf(ub, abs, prec);
        if (arf_is_zero(ub))
            out = -1e9;
        else
            out = arf_get_d(ub, ARF_RND_UP);
        if (out > 0)
            out = log10(out);
        else if (out == 0)
            out = -1e9;
        else
            out = -1e9; /* negative magnitude impossible */
        /* arf_get_d saturates; recompute via mag exponent for tiny values */
        if (!arf_is_zero(ub))
        {
            fmpz_t e;
            fmpz_init(e);
            arf_abs_bound_lt_2exp_fmpz(e, ub);
            out = fmpz_get_d(e) * 0.30102999566398119521;
            fmpz_clear(e);
        }
        arf_clear(ub);
    }
    arb_clear(abs);
    acb_clear(val);
    return out;
}

/* one candidate: LLL at degree maxm, factor, certify.  Returns 1 if found. */
static int
recognize_one(cand_t *c, slong maxm, slong prec)
{
    slong n = maxm + 1;            /* number of relation coefficients */
    slong scale_bits = prec - 32;  /* lattice scaling */
    fmpz_mat_t B;
    acb_t upow;
    arb_t re, im;
    arf_t mid;
    int found = 0;

    if (scale_bits < 64)
        return 0;

    fmpz_mat_init(B, n, n + 2);
    acb_init(upow);
    arb_init(re);
    arb_init(im);
    arf_init(mid);

    /* rows: identity block + scaled Re/Im of u^i */
    acb_one(upow);
    for (slong i = 0; i < n; i++)
    {
        fmpz_one(fmpz_mat_entry(B, i, i));
        arb_mul_2exp_si(re, acb_realref(upow), scale_bits);
        arb_mul_2exp_si(im, acb_imagref(upow), scale_bits);
        arf_set(mid, arb_midref(re));
        arf_get_fmpz(fmpz_mat_entry(B, i, n), mid, ARF_RND_NEAR);
        arf_set(mid, arb_midref(im));
        arf_get_fmpz(fmpz_mat_entry(B, i, n + 1), mid, ARF_RND_NEAR);
        if (i + 1 < n)
            acb_mul(upow, upow, c->u, prec);
    }

    {
        fmpz_lll_t fl;
        fmpz_lll_context_init_default(fl);
        fmpz_lll(B, NULL, fl);
    }

    /* try the few shortest rows as relations */
    for (slong row = 0; row < n && row < 4 && !found; row++)
    {
        fmpz_poly_t rel;
        fmpz_poly_init(rel);
        for (slong i = 0; i < n; i++)
            fmpz_poly_set_coeff_fmpz(rel, i, fmpz_mat_entry(B, row, i));
        if (fmpz_poly_degree(rel) < 1)
        {
            fmpz_poly_clear(rel);
            continue;
        }
        /* certify the relation before factoring.  Two conditions:
         * (a) the residual sits at the exact-relation noise floor,
         *     |rel(u)| <= 10^(-p + log10 H + slack); and
         * (b) the LLL gap test: the relation row is dramatically shorter
         *     than every other row of the reduced basis.  Junk rows have
         *     comparable norms (gap ~ 0 bits); a forced true relation
         *     sits far below the lattice noise. */
        {
            double p10 = prec * 0.30102999566398119521;
            double lr = poly_eval_log10(rel, c->u, prec);
            double log10H = 0;
            for (slong i = 0; i <= fmpz_poly_degree(rel); i++)
            {
                double a = fabs(fmpz_get_d(fmpz_poly_get_coeff_ptr(rel, i)));
                if (a > 1 && log10(a) > log10H) log10H = log10(a);
            }
            double gap = lll_gap_bits(B, row, n, n + 2);
            if (gap < GAP_CERT_BITS || lr > -p10 + log10H + 30)
            {
                fmpz_poly_clear(rel);
                continue;   /* junk relation: precision cannot certify */
            }
        }
        /* factor over Z; certified minimal polynomial = the irreducible
         * factor that vanishes at u */
        {
            fmpz_poly_factor_t fac;
            fmpz_poly_factor_init(fac);
            fmpz_poly_factor(fac, rel);
            for (slong f = 0; f < fac->num && !found; f++)
            {
                fmpz_poly_struct *pf = fac->p + f;
                if (fmpz_poly_degree(pf) < 1)
                    continue;
                double lf = poly_eval_log10(pf, c->u, prec);
                double log10Hf = 0;
                for (slong i = 0; i <= fmpz_poly_degree(pf); i++)
                {
                    double a = fabs(fmpz_get_d(fmpz_poly_get_coeff_ptr(pf, i)));
                    if (a > 1 && log10(a) > log10Hf) log10Hf = log10(a);
                }
                double p10 = prec * 0.30102999566398119521;
                if (lf <= -p10 + log10Hf + 40)
                {
                    fmpz_poly_set(c->minpoly, pf);
                    c->log10resid = lf;
                    found = 1;
                }
            }
            fmpz_poly_factor_clear(fac);
        }
        fmpz_poly_clear(rel);
    }

    fmpz_mat_clear(B);
    acb_clear(upow);
    arb_clear(re);
    arb_clear(im);
    arf_clear(mid);
    return found;
}

static void *
worker(void *arg)
{
    work_t *w = (work_t *) arg;
    for (;;)
    {
        slong i;
        pthread_mutex_lock(&w->mtx);
        i = w->next++;
        pthread_mutex_unlock(&w->mtx);
        if (i >= w->ncand)
            break;
        cand_t *c = &w->cands[i];
        c->status = recognize_one(c, w->maxm, w->prec) ? 1 : -1;
    }
    return NULL;
}

static int
run_file(const char *inpath, const char *outpath)
{
    FILE *fin = fopen(inpath, "r");
    if (!fin) { fprintf(stderr, "cannot open %s\n", inpath); return 1; }
    slong prec, ncand, maxm;
    if (fscanf(fin, "%ld %ld %ld", &prec, &ncand, &maxm) != 3)
    { fprintf(stderr, "bad header\n"); fclose(fin); return 1; }

    cand_t *cands = calloc(ncand, sizeof(cand_t));
    char *buf = malloc(prec + 64);
    for (slong i = 0; i < ncand; i++)
    {
        cands[i].idx = i;
        acb_init(cands[i].u);
        fmpz_poly_init(cands[i].minpoly);
        for (int part = 0; part < 2; part++)
        {
            if (fscanf(fin, "%s", buf) != 1)
            { fprintf(stderr, "bad candidate %ld\n", i); fclose(fin); return 1; }
            arb_set_str(part == 0 ? acb_realref(cands[i].u)
                                  : acb_imagref(cands[i].u), buf, prec);
        }
    }
    fclose(fin);
    free(buf);

    slong nthreads = 1;
    {
        const char *tenv = getenv("MAKEK_RELFINDER_THREADS");
        if (tenv) nthreads = atol(tenv);
        if (nthreads < 1) nthreads = 1;
        if (nthreads > ncand) nthreads = ncand;
    }

    work_t w = { cands, ncand, maxm, prec, 0, PTHREAD_MUTEX_INITIALIZER };
    pthread_t *tids = malloc(nthreads * sizeof(pthread_t));
    for (slong t = 0; t < nthreads; t++)
        pthread_create(&tids[t], NULL, worker, &w);
    for (slong t = 0; t < nthreads; t++)
        pthread_join(tids[t], NULL);
    free(tids);

    FILE *fout = fopen(outpath, "w");
    if (!fout) { fprintf(stderr, "cannot open %s\n", outpath); return 1; }
    slong nfound = 0;
    for (slong i = 0; i < ncand; i++)
    {
        if (cands[i].status == 1)
        {
            nfound++;
            fprintf(fout, "FOUND %ld %ld %.2f", i,
                    fmpz_poly_degree(cands[i].minpoly), cands[i].log10resid);
            for (slong k = 0; k <= fmpz_poly_degree(cands[i].minpoly); k++)
            {
                fprintf(fout, " ");
                fmpz_fprint(fout, fmpz_poly_get_coeff_ptr(cands[i].minpoly, k));
            }
            fprintf(fout, "\n");
        }
        else
            fprintf(fout, "NOPREC %ld\n", i);
        acb_clear(cands[i].u);
        fmpz_poly_clear(cands[i].minpoly);
    }
    fprintf(fout, "RELFINDER_DONE %ld\n", nfound);
    fclose(fout);
    free(cands);
    return 0;
}

/* ---------- selftest ---------- */

static int
selftest(void)
{
    int fails = 0;
    slong prec = 1400;   /* ~420 digits */

    /* 1: u = 2^(1/3) + 5^(1/2), true minpoly degree 6, bound 12 */
    {
        cand_t c;
        c.idx = 0;
        acb_init(c.u);
        fmpz_poly_init(c.minpoly);
        arb_t t;
        arb_init(t);
        arb_set_ui(t, 2);
        arb_root_ui(t, t, 3, prec);
        arb_set(acb_realref(c.u), t);
        arb_sqrt_ui(t, 5, prec);
        arb_add(acb_realref(c.u), acb_realref(c.u), t, prec);
        arb_zero(acb_imagref(c.u));
        if (!recognize_one(&c, 12, prec) || fmpz_poly_degree(c.minpoly) != 6)
        {
            printf("selftest 1 FAILED (deg %ld)\n",
                   c.status == 1 ? fmpz_poly_degree(c.minpoly) : -1);
            fails++;
        }
        else
            printf("selftest 1 ok: deg 6 minpoly at bound 12, log10resid %.1f\n",
                   c.log10resid);
        arb_clear(t);
        acb_clear(c.u);
        fmpz_poly_clear(c.minpoly);
    }

    /* 2: complex u = (1 + i*sqrt(7))/2, degree 2, bound 12 */
    {
        cand_t c;
        acb_init(c.u);
        fmpz_poly_init(c.minpoly);
        arb_t t;
        arb_init(t);
        arb_set_d(acb_realref(c.u), 0.5);
        arb_sqrt_ui(t, 7, prec);
        arb_mul_2exp_si(t, t, -1);
        arb_set(acb_imagref(c.u), t);
        if (!recognize_one(&c, 12, prec) || fmpz_poly_degree(c.minpoly) != 2)
        {
            printf("selftest 2 FAILED\n");
            fails++;
        }
        else
            printf("selftest 2 ok: deg 2 complex minpoly at bound 12\n");
        arb_clear(t);
        acb_clear(c.u);
        fmpz_poly_clear(c.minpoly);
    }

    /* 3: starved precision must report NOPREC, not junk: a degree-8 number
     * with ~40-digit coefficients at 100 bits */
    {
        cand_t c;
        acb_init(c.u);
        fmpz_poly_init(c.minpoly);
        slong lowprec = 100;
        arb_t t;
        arb_init(t);
        /* u = (10^5 + 3)^(1/8) * 2^(1/3): minpoly x^24-ish heights too big */
        arb_set_ui(t, 100003);
        arb_root_ui(t, t, 8, lowprec);
        arb_set(acb_realref(c.u), t);
        arb_set_ui(t, 2);
        arb_root_ui(t, t, 3, lowprec);
        arb_mul(acb_realref(c.u), acb_realref(c.u), t, lowprec);
        arb_zero(acb_imagref(c.u));
        if (recognize_one(&c, 24, lowprec))
        {
            printf("selftest 3 FAILED: certified junk at starved precision\n");
            fails++;
        }
        else
            printf("selftest 3 ok: starved precision -> NOPREC\n");
        arb_clear(t);
        acb_clear(c.u);
        fmpz_poly_clear(c.minpoly);
    }

    if (fails == 0)
        printf("SELFTEST PASSED\n");
    return fails ? 1 : 0;
}

/* ================= --overk mode =================
 *
 * Recognize complex numbers as elements of a KNOWN field K, given the
 * complex embeddings of an integral basis (the RecognizeOverK stage).
 * Sequences are processed with the same denominator chaining as the Magma
 * implementation (prevden multiplies the target, and the found q multiplies
 * into prevden), sequentially within a sequence; certification is per
 * target, so insufficient precision yields a NOPREC verdict instead of a
 * silently wrong element.
 *
 * Input:
 *   line 1: prec_bits  m  nseq
 *   next 2m lines: Re, Im of the m integral-basis embeddings (conjugated
 *                  upstream if needed)
 *   then per sequence: one line "nt", then 2*nt lines Re, Im of targets.
 * Output, per sequence per target (0-based indices):
 *   FOUND <seq> <n> <den> <a_1> ... <a_m>     (target = sum a_i b_i / den)
 *   NOPREC <seq> <n>                          (chain stops for that seq)
 * terminated by "RELFINDER_DONE <nfound>".
 */

typedef struct {
    slong nt;
    acb_ptr t;
    int *status;        /* 1 found, -1 noprec, 0 unprocessed (after a noprec) */
    fmpz_mat_t A;       /* nt x m coordinate rows */
    fmpz *dens;
} oseq_t;

typedef struct {
    oseq_t *seqs;
    slong nseq;
    slong m;
    slong prec;
    acb_ptr basis;
    const fmpz_mat_t *B0;   /* pre-reduced basis block, m x (m+2) */
    slong next;
    pthread_mutex_t mtx;
} owork_t;

static void
overk_seq(oseq_t *s, const acb_ptr basis, slong m, slong prec,
          const fmpz_mat_t B0)
{
    slong scale_bits = prec - 32;
    fmpz_t prevden;
    fmpz_init_set_ui(prevden, 1);

    for (slong n = 0; n < s->nt; n++)
    {
        fmpz_mat_t M;
        acb_t tgt;
        arb_t re, im;
        arf_t mid;
        int ok = 0;
        int cert_flag = 0;

        acb_init(tgt);
        arb_init(re); arb_init(im); arf_init(mid);
        acb_set(tgt, s->t + n);
        {
            /* target row uses -prevden * c */
            acb_t sc;
            acb_init(sc);
            acb_mul_fmpz(sc, tgt, prevden, prec);
            acb_neg(sc, sc);

            fmpz_mat_init(M, m + 1, m + 3);
            /* basis rows: coordinates from B0 cols 0..m-1, scaled cols at the
             * end, and a zero column inserted for the q slot */
            for (slong i = 0; i < m; i++)
            {
                for (slong j = 0; j < m; j++)
                    fmpz_set(fmpz_mat_entry(M, i, j), fmpz_mat_entry(B0, i, j));
                fmpz_set(fmpz_mat_entry(M, i, m + 1), fmpz_mat_entry(B0, i, m));
                fmpz_set(fmpz_mat_entry(M, i, m + 2), fmpz_mat_entry(B0, i, m + 1));
            }
            fmpz_one(fmpz_mat_entry(M, m, m));
            arb_mul_2exp_si(re, acb_realref(sc), scale_bits);
            arf_set(mid, arb_midref(re));
            arf_get_fmpz(fmpz_mat_entry(M, m, m + 1), mid, ARF_RND_NEAR);
            arb_mul_2exp_si(im, acb_imagref(sc), scale_bits);
            arf_set(mid, arb_midref(im));
            arf_get_fmpz(fmpz_mat_entry(M, m, m + 2), mid, ARF_RND_NEAR);
            acb_clear(sc);
        }
        {
            fmpz_lll_t fl;
            fmpz_lll_context_init_default(fl);
            fmpz_lll(M, NULL, fl);
        }
        /* shortest rows: need q != 0 and a certified residual */
        for (slong row = 0; row <= m && !ok; row++)
        {
            const fmpz *q = fmpz_mat_entry(M, row, m);
            if (fmpz_is_zero(q))
                continue;
            /* residual = | sum a_i b_i - q * prevden * c | */
            acb_t acc, term;
            acb_init(acc); acb_init(term);
            acb_zero(acc);
            for (slong i = 0; i < m; i++)
            {
                acb_mul_fmpz(term, basis + i, fmpz_mat_entry(M, row, i), prec);
                acb_add(acc, acc, term, prec);
            }
            acb_mul_fmpz(term, s->t + n, prevden, prec);
            acb_mul_fmpz(term, term, q, prec);
            acb_sub(acc, acc, term, prec);
            {
                arb_t abs;
                fmpz_t e;
                double lr, log10H = 0;
                arb_init(abs);
                fmpz_init(e);
                acb_abs(abs, acc, prec);
                arf_t ub; arf_init(ub);
                arb_get_ubound_arf(ub, abs, prec);
                if (arf_is_zero(ub))
                    lr = -1e9;
                else
                {
                    arf_abs_bound_lt_2exp_fmpz(e, ub);
                    lr = fmpz_get_d(e) * 0.30102999566398119521;
                }
                for (slong i = 0; i <= m; i++)
                {
                    double a = fabs(fmpz_get_d(i < m ? fmpz_mat_entry(M, row, i) : q));
                    if (a > 1 && log10(a) > log10H) log10H = log10(a);
                }
                /* three-tier verdict via the LLL gap test.  CERTIFIED: the
                 * relation row is >= GAP_CERT_BITS shorter than every other
                 * reduced row (a forced relation).  UNCERTIFIED: a modest
                 * gap (>= GAP_UNCERT_BITS) -- the marginal regime the
                 * legacy path silently accepts; tagged for the caller.
                 * No gap: junk, contributes to NOPREC.  Both tiers also
                 * require the residual at the exact-relation noise floor. */
                double p10 = prec * 0.30102999566398119521;
                double gap = lll_gap_bits(M, row, m + 1, m + 3);
                int certified = (gap >= GAP_CERT_BITS);
                if (gap >= GAP_UNCERT_BITS && lr <= -p10 + log10H + 30)
                {
                    /* accept: coords = a, den = q * prevden (sign into a) */
                    fmpz_t den;
                    fmpz_init(den);
                    fmpz_mul(den, q, prevden);
                    if (fmpz_sgn(den) < 0)
                    {
                        fmpz_neg(den, den);
                        for (slong i = 0; i < m; i++)
                            fmpz_neg(fmpz_mat_entry(M, row, i), fmpz_mat_entry(M, row, i));
                    }
                    for (slong i = 0; i < m; i++)
                        fmpz_set(fmpz_mat_entry(s->A, n, i), fmpz_mat_entry(M, row, i));
                    fmpz_set(s->dens + n, den);
                    fmpz_t qa;
                    fmpz_init(qa);
                    fmpz_abs(qa, q);
                    fmpz_mul(prevden, prevden, qa);
                    fmpz_clear(qa);
                    fmpz_clear(den);
                    ok = 1;
                    cert_flag = certified;
                }
                arf_clear(ub);
                arb_clear(abs);
                fmpz_clear(e);
            }
            acb_clear(acc); acb_clear(term);
        }
        fmpz_mat_clear(M);
        acb_clear(tgt);
        arb_clear(re); arb_clear(im); arf_clear(mid);

        if (!ok)
        {
            s->status[n] = -1;
            /* chain is broken; remaining targets unprocessed */
            break;
        }
        s->status[n] = cert_flag ? 1 : 2;
    }
    fmpz_clear(prevden);
}

static void *
oworker(void *arg)
{
    owork_t *w = (owork_t *) arg;
    for (;;)
    {
        slong i;
        pthread_mutex_lock(&w->mtx);
        i = w->next++;
        pthread_mutex_unlock(&w->mtx);
        if (i >= w->nseq)
            break;
        overk_seq(&w->seqs[i], w->basis, w->m, w->prec, *w->B0);
    }
    return NULL;
}

static int
run_overk(const char *inpath, const char *outpath)
{
    FILE *fin = fopen(inpath, "r");
    if (!fin) { fprintf(stderr, "cannot open %s\n", inpath); return 1; }
    slong prec, m, nseq;
    if (fscanf(fin, "%ld %ld %ld", &prec, &m, &nseq) != 3)
    { fprintf(stderr, "bad header\n"); fclose(fin); return 1; }

    char *buf = malloc(prec + 64);
    acb_ptr basis = _acb_vec_init(m);
    for (slong i = 0; i < m; i++)
        for (int part = 0; part < 2; part++)
        {
            if (fscanf(fin, "%s", buf) != 1)
            { fprintf(stderr, "bad basis\n"); fclose(fin); return 1; }
            arb_set_str(part == 0 ? acb_realref(basis + i)
                                  : acb_imagref(basis + i), buf, prec);
        }

    oseq_t *seqs = calloc(nseq, sizeof(oseq_t));
    for (slong sidx = 0; sidx < nseq; sidx++)
    {
        oseq_t *s = &seqs[sidx];
        if (fscanf(fin, "%ld", &s->nt) != 1)
        { fprintf(stderr, "bad seq header\n"); fclose(fin); return 1; }
        s->t = _acb_vec_init(s->nt);
        s->status = calloc(s->nt, sizeof(int));
        fmpz_mat_init(s->A, s->nt, m);
        s->dens = _fmpz_vec_init(s->nt);
        for (slong n = 0; n < s->nt; n++)
            for (int part = 0; part < 2; part++)
            {
                if (fscanf(fin, "%s", buf) != 1)
                { fprintf(stderr, "bad target\n"); fclose(fin); return 1; }
                arb_set_str(part == 0 ? acb_realref(s->t + n)
                                      : acb_imagref(s->t + n), buf, prec);
            }
    }
    fclose(fin);
    free(buf);

    /* pre-reduce the basis block once: m rows, [I | scaled Re | scaled Im] */
    fmpz_mat_t B0;
    {
        slong scale_bits = prec - 32;
        arb_t sc;
        arf_t mid;
        arb_init(sc);
        arf_init(mid);
        fmpz_mat_init(B0, m, m + 2);
        for (slong i = 0; i < m; i++)
        {
            fmpz_one(fmpz_mat_entry(B0, i, i));
            arb_mul_2exp_si(sc, acb_realref(basis + i), scale_bits);
            arf_set(mid, arb_midref(sc));
            arf_get_fmpz(fmpz_mat_entry(B0, i, m), mid, ARF_RND_NEAR);
            arb_mul_2exp_si(sc, acb_imagref(basis + i), scale_bits);
            arf_set(mid, arb_midref(sc));
            arf_get_fmpz(fmpz_mat_entry(B0, i, m + 1), mid, ARF_RND_NEAR);
        }
        fmpz_lll_t fl;
        fmpz_lll_context_init_default(fl);
        fmpz_lll(B0, NULL, fl);
        arb_clear(sc);
        arf_clear(mid);
    }

    slong nthreads = 1;
    {
        const char *tenv = getenv("MAKEK_RELFINDER_THREADS");
        if (tenv) nthreads = atol(tenv);
        if (nthreads < 1) nthreads = 1;
        if (nthreads > nseq) nthreads = nseq;
    }
    owork_t w = { seqs, nseq, m, prec, basis, (const fmpz_mat_t *) &B0, 0,
                  PTHREAD_MUTEX_INITIALIZER };
    pthread_t *tids = malloc(nthreads * sizeof(pthread_t));
    for (slong t = 0; t < nthreads; t++)
        pthread_create(&tids[t], NULL, oworker, &w);
    for (slong t = 0; t < nthreads; t++)
        pthread_join(tids[t], NULL);
    free(tids);

    FILE *fout = fopen(outpath, "w");
    if (!fout) { fprintf(stderr, "cannot open %s\n", outpath); return 1; }
    slong nfound = 0;
    for (slong sidx = 0; sidx < nseq; sidx++)
    {
        oseq_t *s = &seqs[sidx];
        for (slong n = 0; n < s->nt; n++)
        {
            if (s->status[n] == 1 || s->status[n] == 2)
            {
                nfound++;
                fprintf(fout, "%s %ld %ld ",
                        s->status[n] == 1 ? "FOUND" : "UNCERT", sidx, n);
                fmpz_fprint(fout, s->dens + n);
                for (slong i = 0; i < m; i++)
                {
                    fprintf(fout, " ");
                    fmpz_fprint(fout, fmpz_mat_entry(s->A, n, i));
                }
                fprintf(fout, "\n");
            }
            else if (s->status[n] == -1)
                fprintf(fout, "NOPREC %ld %ld\n", sidx, n);
            /* status 0 (after a break) intentionally unreported */
        }
        _acb_vec_clear(s->t, s->nt);
        free(s->status);
        fmpz_mat_clear(s->A);
        _fmpz_vec_clear(s->dens, s->nt);
    }
    fprintf(fout, "RELFINDER_DONE %ld\n", nfound);
    fclose(fout);
    free(seqs);
    fmpz_mat_clear(B0);
    _acb_vec_clear(basis, m);
    return 0;
}

static int
selftest_overk(void)
{
    int fails = 0;
    slong prec = 700;
    slong m = 2;
    acb_ptr basis = _acb_vec_init(m);
    /* K = Q(sqrt 5), integral basis 1, (1+sqrt5)/2 */
    arb_t s5;
    arb_init(s5);
    arb_sqrt_ui(s5, 5, prec);
    acb_one(basis + 0);
    arb_add_ui(acb_realref(basis + 1), s5, 1, prec);
    arb_mul_2exp_si(acb_realref(basis + 1), acb_realref(basis + 1), -1);

    fmpz_mat_t B0;
    {
        slong scale_bits = prec - 32;
        arb_t sc; arf_t mid;
        arb_init(sc); arf_init(mid);
        fmpz_mat_init(B0, m, m + 2);
        for (slong i = 0; i < m; i++)
        {
            fmpz_one(fmpz_mat_entry(B0, i, i));
            arb_mul_2exp_si(sc, acb_realref(basis + i), scale_bits);
            arf_set(mid, arb_midref(sc));
            arf_get_fmpz(fmpz_mat_entry(B0, i, m), mid, ARF_RND_NEAR);
            arb_mul_2exp_si(sc, acb_imagref(basis + i), scale_bits);
            arf_set(mid, arb_midref(sc));
            arf_get_fmpz(fmpz_mat_entry(B0, i, m + 1), mid, ARF_RND_NEAR);
        }
        fmpz_lll_t fl;
        fmpz_lll_context_init_default(fl);
        fmpz_lll(B0, NULL, fl);
        arb_clear(sc); arf_clear(mid);
    }

    /* sequence: (3 + 7*phi)/5 then (-2 + 9*phi)/40 (chained denominators) */
    oseq_t s;
    s.nt = 2;
    s.t = _acb_vec_init(2);
    s.status = calloc(2, sizeof(int));
    fmpz_mat_init(s.A, 2, m);
    s.dens = _fmpz_vec_init(2);
    acb_mul_ui(s.t + 0, basis + 1, 7, prec);
    acb_add_ui(s.t + 0, s.t + 0, 3, prec);
    acb_div_ui(s.t + 0, s.t + 0, 5, prec);
    acb_mul_ui(s.t + 1, basis + 1, 9, prec);
    acb_sub_ui(s.t + 1, s.t + 1, 2, prec);
    acb_div_ui(s.t + 1, s.t + 1, 40, prec);

    overk_seq(&s, basis, m, prec, B0);
    if (s.status[0] != 1 || s.status[1] != 1
        || fmpz_cmp_ui(s.dens + 0, 5) != 0
        || fmpz_cmp_ui(fmpz_mat_entry(s.A, 0, 1), 7) != 0)
    {
        printf("overk selftest 1 FAILED\n");
        fails++;
    }
    else
        printf("overk selftest 1 ok: chained denominators recovered\n");

    /* pi is not in K: must be NOPREC, not junk */
    oseq_t s2;
    s2.nt = 1;
    s2.t = _acb_vec_init(1);
    s2.status = calloc(1, sizeof(int));
    fmpz_mat_init(s2.A, 1, m);
    s2.dens = _fmpz_vec_init(1);
    arb_const_pi(acb_realref(s2.t + 0), prec);
    overk_seq(&s2, basis, m, prec, B0);
    if (s2.status[0] != -1)
    {
        printf("overk selftest 2 FAILED: certified junk for pi\n");
        fails++;
    }
    else
        printf("overk selftest 2 ok: non-element -> NOPREC\n");

    _acb_vec_clear(s.t, 2); free(s.status); fmpz_mat_clear(s.A); _fmpz_vec_clear(s.dens, 2);
    _acb_vec_clear(s2.t, 1); free(s2.status); fmpz_mat_clear(s2.A); _fmpz_vec_clear(s2.dens, 1);
    fmpz_mat_clear(B0);
    arb_clear(s5);
    _acb_vec_clear(basis, m);
    return fails;
}

int
main(int argc, char **argv)
{
    if (argc == 2 && strcmp(argv[1], "--selftest") == 0)
    {
        int f = selftest();
        f += selftest_overk();
        if (f == 0)
            printf("SELFTEST PASSED (both modes)\n");
        return f ? 1 : 0;
    }
    if (argc == 4 && strcmp(argv[1], "--overk") == 0)
        return run_overk(argv[2], argv[3]);
    if (argc != 3)
    {
        fprintf(stderr, "usage: %s in.txt out.txt | --overk in.txt out.txt | --selftest\n", argv[0]);
        return 2;
    }
    return run_file(argv[1], argv[2]);
}
