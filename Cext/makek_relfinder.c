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
        /* certify the relation itself before factoring: |rel(u)| must be
         * far below what the lattice scaling alone enforces */
        {
            double lr = poly_eval_log10(rel, c->u, prec);
            double H = 0;
            for (slong i = 0; i <= fmpz_poly_degree(rel); i++)
            {
                double a = fmpz_get_d(fmpz_poly_get_coeff_ptr(rel, i));
                a = fabs(a);
                if (a > H) H = a;
            }
            double log10H = (H > 0) ? log10(H) : 0;
            double budget = -(prec * 0.30102999566398119521) / 2.0 + log10H;
            if (lr > budget)
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
                double budget = -(prec * 0.30102999566398119521) / 3.0;
                if (lf < budget)
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

int
main(int argc, char **argv)
{
    if (argc == 2 && strcmp(argv[1], "--selftest") == 0)
        return selftest();
    if (argc != 3)
    {
        fprintf(stderr, "usage: %s in.txt out.txt | --selftest\n", argv[0]);
        return 2;
    }
    return run_file(argv[1], argv[2]);
}
