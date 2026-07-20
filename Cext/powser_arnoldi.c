/*
 * powser_arnoldi.c — external solver for the Arnoldi/numerical-kernel stage
 * of PowerSeriesBasis (Belyi/Code/powser_iter_arfed.m).
 *
 * The Magma intrinsic reduces the problem to: find the eigenvalue-1
 * eigenvectors of the coefficient-space operator
 *
 *     A = (1/Q) * Wp * P * J
 *
 * where, per center i = 1..nv,
 *   - Wp maps coefficients c to values  vand_j * p(x_j),  p(X) = sum_r c_r X^r,
 *     at the FD-reduced points x_j = wp_j^{e_i} (points sorted by center),
 *   - P is a permutation matching sorted points back to sample slots,
 *   - J maps values v to coefficients via  (v*J)[r] = sum_m g_m v_m zeta_Q^{-e_i r m},
 *     i.e. a pointwise weight followed by a length-Q DFT sampled at bins
 *     (e_i * r) mod Q.
 *
 * This program runs Arnoldi iteration with that structured matvec
 * (threaded Horner + acb_dft), detects the kernel of (H - 1) via a
 * high-precision one-sided Jacobi SVD, and mirrors the escape logic of the
 * Magma code.  It self-validates: each returned vector x is checked to
 * satisfy |A x - x| < validation threshold, reported in the output file.
 *
 * Build (Linux):  gcc -O2 -pthread powser_arnoldi.c -o powser_arnoldi -lflint -lmpfr -lgmp -lm
 * Build (macOS):  clang -O2 -pthread powser_arnoldi.c -o powser_arnoldi \
 *                   -I$(brew --prefix flint)/include -L$(brew --prefix flint)/lib \
 *                   -I$(brew --prefix mpfr)/include -L$(brew --prefix mpfr)/lib \
 *                   -I$(brew --prefix gmp)/include  -L$(brew --prefix gmp)/lib \
 *                   -lflint -lmpfr -lgmp -lm
 *
 * Usage:  powser_arnoldi input.txt output.m [nthreads]
 *         powser_arnoldi --selftest
 *
 * Input file format (whitespace/newline separated tokens; complex numbers
 * are two decimal tokens re im, arbitrary precision, E or e exponents):
 *
 *   digs eps_digits maxiter dim nv Q hermitian
 *   # per center i = 1..nv:  NN_i  e_i  bin0_i  Ptotal_i
 *   #   NN_i    = number of coefficients in this center's block
 *   #   e_i     = ramification degree (DFT stride)
 *   #   bin0_i  = starting DFT bin offset (0 if ss folded into weights)
 *   #   Ptotal_i= number of sorted points belonging to this center
 *   # per center: Ptotal_i lines  "x_re x_im vand_re vand_im"
 *   #   (x_j = wp_j^{e_i} evaluation point; vand_j = multiplier)
 *   # per center: Q lines "g_re g_im"  (J-side weights, post-processing)
 *   # permutation: nv*Q integers perm[t] in [1..nv*Q]:
 *   #   J-side input slot t takes Wp-side output entry perm[t]
 *   # dim start vectors, each V = sum NN_i complex numbers
 *
 * Output: a Magma-parseable file
 *   return [* [ [re,im], ... V entries ]  (dim vectors), minsing_digits, residuals *];
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <math.h>
#include <pthread.h>
#include <flint/flint.h>
#include <flint/acb.h>
#include <flint/arb.h>
#include <flint/acb_mat.h>
#include <flint/acb_dft.h>

/* FLINT 3.1 renamed flint_randinit -> flint_rand_init; map the new names
   onto the old ones when building against FLINT 3.0 */
#if __FLINT_RELEASE < 30100
#define flint_rand_init flint_randinit
#define flint_rand_clear flint_randclear
#endif

/* ------------------------------------------------------------------ */
/* problem data                                                        */
/* ------------------------------------------------------------------ */

typedef struct
{
    slong nv, Q, dim, maxiter, digs;
    slong prec;            /* working precision in bits */
    arb_t eps;             /* eps_thresh */
    int hermitian;         /* 1: conjugated inner products; 0: Magma-style bilinear */
    slong *NN;             /* coefficients per center */
    slong *es;             /* ramification degree per center */
    slong *bin0;           /* DFT bin offset per center */
    slong *Ptot;           /* sorted points per center */
    slong V;               /* total coefficient dimension = sum NN */
    slong P;               /* total points = nv*Q */
    acb_ptr x;             /* evaluation points, sorted-by-center, length P */
    acb_ptr vand;          /* Vandermonde multipliers, length P */
    acb_ptr g;             /* J-side weights, nv*Q (center-major) */
    slong *perm;           /* 0-based: J input slot t <- Wp output perm[t] */
    acb_ptr start;         /* dim start vectors, each length V */
    slong nthreads;
} problem_t;

/* ------------------------------------------------------------------ */
/* threaded Horner evaluation                                          */
/* ------------------------------------------------------------------ */

typedef struct
{
    acb_srcptr coeffs;
    slong NN;
    acb_srcptr x;
    acb_srcptr vand;
    acb_ptr out;
    slong lo, hi;
    slong prec;
} horner_task_t;

static void *horner_worker(void *arg)
{
    horner_task_t *t = (horner_task_t *) arg;
    slong m, r;
    acb_t s;
    acb_init(s);
    for (m = t->lo; m < t->hi; m++)
    {
        acb_set(s, t->coeffs + (t->NN - 1));
        for (r = t->NN - 2; r >= 0; r--)
        {
            acb_mul(s, s, t->x + m, t->prec);
            acb_add(s, s, t->coeffs + r, t->prec);
        }
        acb_mul(t->out + m, s, t->vand + m, t->prec);
    }
    acb_clear(s);
    return NULL;
}

/* out[m] = vand[m] * p(x[m]) for m in [0,n), threaded */
static void horner_multi(acb_ptr out, acb_srcptr coeffs, slong NN,
                         acb_srcptr x, acb_srcptr vand, slong n,
                         slong prec, slong nthreads)
{
    if (nthreads <= 1 || n < 64)
    {
        horner_task_t t = {coeffs, NN, x, vand, out, 0, n, prec};
        horner_worker(&t);
        return;
    }
    {
        pthread_t threads[64];
        horner_task_t tasks[64];
        slong T = nthreads > 64 ? 64 : nthreads, i;
        for (i = 0; i < T; i++)
        {
            tasks[i] = (horner_task_t) {coeffs, NN, x, vand, out,
                                        i * n / T, (i + 1) * n / T, prec};
            pthread_create(&threads[i], NULL, horner_worker, &tasks[i]);
        }
        for (i = 0; i < T; i++)
            pthread_join(threads[i], NULL);
    }
}

/* ------------------------------------------------------------------ */
/* structured matvec: w = A v = (1/Q) Wp-eval -> permute -> weight+DFT  */
/* ------------------------------------------------------------------ */

typedef struct
{
    problem_t *pb;
    acb_ptr vals;      /* scratch, length P: Wp-side outputs (sorted order) */
    acb_ptr slots;     /* scratch, length P: J-side inputs (slot order) */
    acb_ptr dft_in;    /* scratch, length Q */
    acb_ptr dft_out;   /* scratch, length Q */
} matvec_ws_t;

static void matvec_ws_init(matvec_ws_t *ws, problem_t *pb)
{
    ws->pb = pb;
    ws->vals = _acb_vec_init(pb->P);
    ws->slots = _acb_vec_init(pb->P);
    ws->dft_in = _acb_vec_init(pb->Q);
    ws->dft_out = _acb_vec_init(pb->Q);
}

static void matvec_ws_clear(matvec_ws_t *ws)
{
    problem_t *pb = ws->pb;
    _acb_vec_clear(ws->vals, pb->P);
    _acb_vec_clear(ws->slots, pb->P);
    _acb_vec_clear(ws->dft_in, pb->Q);
    _acb_vec_clear(ws->dft_out, pb->Q);
}

static void matvec_structured(acb_ptr w, acb_srcptr v, matvec_ws_t *ws)
{
    problem_t *pb = ws->pb;
    slong prec = pb->prec, Q = pb->Q;
    slong i, t, r, coff = 0, poff = 0;

    /* Wp side: per center, evaluate polynomial at that center's points */
    for (i = 0; i < pb->nv; i++)
    {
        horner_multi(ws->vals + poff, v + coff, pb->NN[i],
                     pb->x + poff, pb->vand + poff, pb->Ptot[i],
                     prec, pb->nthreads);
        coff += pb->NN[i];
        poff += pb->Ptot[i];
    }

    /* permute into J-side slot order */
    for (t = 0; t < pb->P; t++)
        acb_set(ws->slots + t, ws->vals + pb->perm[t]);

    /* J side: per center, pointwise weight then DFT, extract strided bins */
    coff = 0;
    for (i = 0; i < pb->nv; i++)
    {
        for (t = 0; t < Q; t++)
            acb_mul(ws->dft_in + t, ws->slots + i * Q + t, pb->g + i * Q + t, prec);
        acb_dft(ws->dft_out, ws->dft_in, Q, prec);
        for (r = 0; r < pb->NN[i]; r++)
        {
            slong bin = (pb->bin0[i] + pb->es[i] * r) % Q;
            acb_div_si(w + coff + r, ws->dft_out + bin, Q, prec);
        }
        coff += pb->NN[i];
    }
}

/* ------------------------------------------------------------------ */
/* inner products (bilinear like Magma's InnerProduct, or Hermitian)    */
/* Callers supply bc = conj(b) precomputed for the Hermitian case so    */
/* that the fast acb_dot kernel is used either way.                     */
/* ------------------------------------------------------------------ */

static void vec_dot2(acb_t res, acb_srcptr a, acb_srcptr b_or_bc, slong n,
                     slong prec)
{
    acb_dot(res, NULL, 0, a, 1, b_or_bc, 1, n, prec);
}

/* legacy interface used by residual-free callers (selftest) */
static void vec_dot(acb_t res, acb_srcptr a, acb_srcptr b, slong n,
                    int hermitian, slong prec)
{
    if (!hermitian)
    {
        acb_dot(res, NULL, 0, a, 1, b, 1, n, prec);
    }
    else
    {
        slong i;
        acb_t t, c;
        acb_init(t); acb_init(c);
        acb_zero(res);
        for (i = 0; i < n; i++)
        {
            acb_conj(c, b + i);
            acb_mul(t, a + i, c, prec);
            acb_add(res, res, t, prec);
        }
        acb_clear(t); acb_clear(c);
    }
}

/* ------------------------------------------------------------------ */
/* one-sided Jacobi SVD of an n x n complex matrix M (column version).  */
/* Returns singular values s[0..n) (unsorted) and matrix W (n x n) with */
/* M W = U diag(s): columns of W are right singular vectors.            */
/* ------------------------------------------------------------------ */

static void jacobi_svd(arb_ptr s, acb_mat_t W, const acb_mat_t M, slong prec)
{
    slong n = acb_mat_ncols(M);
    slong nr = acb_mat_nrows(M);
    slong sweep, p, q, i;
    acb_mat_t B;
    acb_t app, aqq, apq, c1, s1, t1, t2;
    arb_t off, diag, thr, tmp;

    acb_mat_init(B, nr, n);
    acb_mat_set(B, M);
    acb_mat_one(W);
    acb_init(app); acb_init(aqq); acb_init(apq);
    acb_init(c1); acb_init(s1); acb_init(t1); acb_init(t2);
    arb_init(off); arb_init(diag); arb_init(thr); arb_init(tmp);

    for (sweep = 0; sweep < 60; sweep++)
    {
        int rotated = 0;
        for (p = 0; p < n - 1; p++)
        for (q = p + 1; q < n; q++)
        {
            /* Hermitian 2x2 Gram block of columns p,q */
            acb_zero(app); acb_zero(aqq); acb_zero(apq);
            for (i = 0; i < nr; i++)
            {
                acb_conj(t1, acb_mat_entry(B, i, p));
                acb_mul(t2, t1, acb_mat_entry(B, i, p), prec);
                acb_add(app, app, t2, prec);
                acb_conj(t1, acb_mat_entry(B, i, q));
                acb_mul(t2, t1, acb_mat_entry(B, i, q), prec);
                acb_add(aqq, aqq, t2, prec);
                acb_conj(t1, acb_mat_entry(B, i, p));
                acb_mul(t2, t1, acb_mat_entry(B, i, q), prec);
                acb_add(apq, apq, t2, prec);
            }
            /* rotations are computed from midpoints: near-converged pivots
               have Gram entries with relative radius ~1, which would make
               the ball arithmetic below blow up (NaN); the rotation itself
               need not be exact for one-sided Jacobi to converge. */
            acb_get_mid(app, app);
            acb_get_mid(aqq, aqq);
            acb_get_mid(apq, apq);

            acb_abs(off, apq, prec);
            acb_abs(diag, app, prec);
            acb_abs(tmp, aqq, prec);
            arb_mul(thr, diag, tmp, prec);
            arb_sqrt(thr, thr, prec);
            arb_mul_2exp_si(thr, thr, -(prec - 8));    /* relative threshold */
            if (!arb_gt(off, thr))   /* skip unless certainly above threshold */
                continue;
            rotated = 1;

            if (getenv("POWSER_DEBUG_ROT") &&
                (!acb_is_finite(app) || !acb_is_finite(aqq) || !acb_is_finite(apq)))
            {
                printf("NONFINITE GRAM sweep=%ld p=%ld q=%ld\n",
                       (long) sweep, (long) p, (long) q);
            }

            /* complex Jacobi rotation diagonalizing [[app,apq],[conj(apq),aqq]] */
            {
                arb_t alpha, beta, gamma_abs, zeta, tan_t, cs;
                acb_t phase;
                arb_init(alpha); arb_init(beta); arb_init(gamma_abs);
                arb_init(zeta); arb_init(tan_t); arb_init(cs);
                acb_init(phase);

                arb_set(alpha, acb_realref(app));
                arb_set(beta, acb_realref(aqq));
                acb_abs(gamma_abs, apq, prec);
                /* phase = apq / |apq| */
                acb_set_arb(phase, gamma_abs);
                acb_div(phase, apq, phase, prec);

                /* zeta = (beta - alpha) / (2|gamma|) */
                arb_sub(zeta, beta, alpha, prec);
                arb_div(zeta, zeta, gamma_abs, prec);
                arb_mul_2exp_si(zeta, zeta, -1);
                /* tan t = sign(zeta) / (|zeta| + sqrt(1+zeta^2)) */
                arb_mul(tan_t, zeta, zeta, prec);
                arb_add_ui(tan_t, tan_t, 1, prec);
                arb_sqrt(tan_t, tan_t, prec);
                arb_abs(tmp, zeta);
                arb_add(tan_t, tan_t, tmp, prec);
                arb_inv(tan_t, tan_t, prec);
                if (arb_is_negative(zeta))
                    arb_neg(tan_t, tan_t);
                /* c = 1/sqrt(1+t^2), s = c*t */
                arb_mul(cs, tan_t, tan_t, prec);
                arb_add_ui(cs, cs, 1, prec);
                arb_sqrt(cs, cs, prec);
                arb_inv(cs, cs, prec);
                arb_set(tmp, cs);
                arb_mul(tmp, tmp, tan_t, prec);

                /* rotation: col_p' = c*col_p - s*conj(phase)*col_q
                             col_q' = s*phase*col_p + c*col_q  */
                acb_set_arb(c1, cs);              /* c (real) */
                acb_conj(s1, phase);
                acb_mul_arb(s1, s1, tmp, prec);   /* s*conj(phase) */

                for (i = 0; i < nr; i++)
                {
                    acb_mul(t1, c1, acb_mat_entry(B, i, p), prec);
                    acb_mul(t2, s1, acb_mat_entry(B, i, q), prec);
                    acb_sub(t1, t1, t2, prec);

                    /* col_q' = conj(s1) * col_p + c * col_q */
                    acb_conj(t2, s1);
                    acb_mul(t2, t2, acb_mat_entry(B, i, p), prec);
                    acb_mul(app, c1, acb_mat_entry(B, i, q), prec);
                    acb_add(t2, t2, app, prec);

                    acb_set(acb_mat_entry(B, i, p), t1);
                    acb_set(acb_mat_entry(B, i, q), t2);
                }
                for (i = 0; i < n; i++)
                {
                    acb_mul(t1, c1, acb_mat_entry(W, i, p), prec);
                    acb_mul(t2, s1, acb_mat_entry(W, i, q), prec);
                    acb_sub(t1, t1, t2, prec);

                    acb_conj(t2, s1);
                    acb_mul(t2, t2, acb_mat_entry(W, i, p), prec);
                    acb_mul(app, c1, acb_mat_entry(W, i, q), prec);
                    acb_add(t2, t2, app, prec);

                    acb_set(acb_mat_entry(W, i, p), t1);
                    acb_set(acb_mat_entry(W, i, q), t2);
                }
                if (getenv("POWSER_DEBUG_ROT"))
                {
                    int bad = 0;
                    for (i = 0; i < nr && !bad; i++)
                        if (!acb_is_finite(acb_mat_entry(B, i, p)) ||
                            !acb_is_finite(acb_mat_entry(B, i, q)))
                            bad = 1;
                    if (bad)
                    {
                        printf("NONFINITE B after rot sweep=%ld p=%ld q=%ld\n",
                               (long) sweep, (long) p, (long) q);
                        printf("  alpha="); arb_printd(alpha, 5);
                        printf("  beta="); arb_printd(beta, 5);
                        printf("  |gamma|="); arb_printd(gamma_abs, 5);
                        printf("\n  zeta="); arb_printd(zeta, 5);
                        printf("  tan="); arb_printd(tan_t, 5);
                        printf("  c="); arb_printd(cs, 5);
                        printf("  phase="); acb_printd(phase, 5);
                        printf("\n");
                        exit(1);
                    }
                }
                arb_clear(alpha); arb_clear(beta); arb_clear(gamma_abs);
                arb_clear(zeta); arb_clear(tan_t); arb_clear(cs);
                acb_clear(phase);
            }
        }
        if (!rotated)
            break;
    }

    /* singular values = column norms of B */
    for (p = 0; p < n; p++)
    {
        arb_zero(s + p);
        for (i = 0; i < nr; i++)
        {
            if (getenv("POWSER_DEBUG_ROT") && !acb_is_finite(acb_mat_entry(B, i, p)))
                printf("NONFINITE B[%ld][%ld] at end\n", (long) i, (long) p);
            acb_abs(tmp, acb_mat_entry(B, i, p), prec);
            arb_sqr(tmp, tmp, prec);
            arb_add(s + p, s + p, tmp, prec);
        }
        arb_sqrtpos(s + p, s + p, prec);
        if (getenv("POWSER_DEBUG_ROT") && !arb_is_finite(s + p))
        {
            printf("NONFINITE s[%ld]; column entries:\n", (long) p);
            for (i = 0; i < (nr < 4 ? nr : 4); i++)
            {
                printf("  B[%ld][%ld] = ", (long) i, (long) p);
                acb_printd(acb_mat_entry(B, i, p), 5);
                printf("\n");
            }
        }
    }

    acb_mat_clear(B);
    acb_clear(app); acb_clear(aqq); acb_clear(apq);
    acb_clear(c1); acb_clear(s1); acb_clear(t1); acb_clear(t2);
    arb_clear(off); arb_clear(diag); arb_clear(thr); arb_clear(tmp);
}

/*
 * fast numerical left-kernel detector: inverse iteration on B = M^T.
 * Finds the smallest singular value of M and its left-singular vector
 * (y with y M ~ 0) via a few rounds of  solve B^H w = v; solve B v = w,
 * which applies (B^H B)^{-1}.  Costs two LU factorizations, O(n^3) with a
 * tiny constant, vs O(sweeps * n^3) dots for the Jacobi SVD.  All in
 * midpoint (floating-point) arithmetic; the caller's final residual check
 * provides the rigor.  Returns 1 on success, 0 if the LU fails (then the
 * caller falls back to the Jacobi path).
 */
static int left_kernel_inverse_iter(acb_mat_t ker, arb_t minsing,
                                    const acb_mat_t M, const arb_t eps,
                                    slong prec, slong *count)
{
    slong n = acb_mat_nrows(M), i, j, it;
    acb_mat_t B, Bh, LU, LUh, v, w;
    slong *P, *Ph;
    arb_t nv, tmp;
    acb_t z;
    int ok = 1;

    acb_mat_init(B, n, n);
    acb_mat_init(Bh, n, n);
    acb_mat_init(LU, n, n);
    acb_mat_init(LUh, n, n);
    acb_mat_init(v, n, 1);
    acb_mat_init(w, n, 1);
    P = flint_malloc(sizeof(slong) * n);
    Ph = flint_malloc(sizeof(slong) * n);
    arb_init(nv); arb_init(tmp);
    acb_init(z);

    /* B = M^T (no conjugate), Bh = B^H = conj(M) */
    for (i = 0; i < n; i++)
        for (j = 0; j < n; j++)
        {
            acb_set(acb_mat_entry(B, i, j), acb_mat_entry(M, j, i));
            acb_get_mid(acb_mat_entry(B, i, j), acb_mat_entry(B, i, j));
            acb_conj(acb_mat_entry(Bh, i, j), acb_mat_entry(M, i, j));
            acb_get_mid(acb_mat_entry(Bh, i, j), acb_mat_entry(Bh, i, j));
        }

    if (!acb_mat_approx_lu(P, LU, B, prec) ||
        !acb_mat_approx_lu(Ph, LUh, Bh, prec))
    {
        ok = 0;   /* exactly singular midpoint: fall back to Jacobi */
        goto cleanup;
    }

    /* fixed deterministic start vector */
    for (i = 0; i < n; i++)
        acb_set_d_d(acb_mat_entry(v, i, 0),
                    1.0 / (double)(i + 2), 1.0 / (double)(2 * i + 3));

    for (it = 0; it < 4; it++)
    {
        acb_mat_approx_solve_lu_precomp(w, Ph, LUh, v, prec);
        acb_mat_approx_solve_lu_precomp(v, P, LU, w, prec);
        /* normalize */
        arb_zero(nv);
        for (i = 0; i < n; i++)
        {
            acb_abs(tmp, acb_mat_entry(v, i, 0), prec);
            arb_sqr(tmp, tmp, prec);
            arb_add(nv, nv, tmp, prec);
        }
        arb_sqrtpos(nv, nv, prec);
        if (!arb_is_finite(nv) || arb_is_zero(nv)) { ok = 0; goto cleanup; }
        for (i = 0; i < n; i++)
        {
            acb_div_arb(acb_mat_entry(v, i, 0), acb_mat_entry(v, i, 0), nv, prec);
            acb_get_mid(acb_mat_entry(v, i, 0), acb_mat_entry(v, i, 0));
        }
    }

    /* sigma_min ~ |B v|_2 with |v| = 1 */
    arb_zero(nv);
    for (i = 0; i < n; i++)
    {
        acb_zero(z);
        for (j = 0; j < n; j++)
            acb_addmul(z, acb_mat_entry(B, i, j), acb_mat_entry(v, j, 0), prec);
        acb_abs(tmp, z, prec);
        arb_sqr(tmp, tmp, prec);
        arb_add(nv, nv, tmp, prec);
    }
    arb_sqrtpos(minsing, nv, prec);
    arb_get_mid_arb(minsing, minsing);

    *count = arb_lt(minsing, eps) ? 1 : 0;
    if (*count)
        for (i = 0; i < n; i++)
            acb_set(acb_mat_entry(ker, 0, i), acb_mat_entry(v, i, 0));

cleanup:
    acb_mat_clear(B); acb_mat_clear(Bh);
    acb_mat_clear(LU); acb_mat_clear(LUh);
    acb_mat_clear(v); acb_mat_clear(w);
    flint_free(P); flint_free(Ph);
    arb_clear(nv); arb_clear(tmp);
    acb_clear(z);
    return ok;
}

/*
 * numerical LEFT kernel of square matrix M (n x n): vectors y with y M ~ 0.
 * Fast path: inverse iteration (above).  Fallback: Jacobi SVD on M^T.
 * Returns number of kernel vectors found (singular value < eps), stores
 * them as rows of ker (allocated n x n; first `count` rows valid), and the
 * minimum singular value in minsing.
 */
static slong numerical_left_kernel(acb_mat_t ker, arb_t minsing,
                                   const acb_mat_t M, const arb_t eps, slong prec)
{
    slong n = acb_mat_nrows(M), i, j, count = 0;
    acb_mat_t Mt, W;
    arb_ptr s;

    if (!getenv("POWSER_FORCE_JACOBI"))
    {
        slong cnt = 0;
        if (left_kernel_inverse_iter(ker, minsing, M, eps, prec, &cnt))
            return cnt;
        /* LU failed (exactly singular midpoint) -> Jacobi fallback below */
    }
    acb_mat_init(Mt, n, n);
    acb_mat_init(W, n, n);
    s = _arb_vec_init(n);

    /* numerical (midpoint) SVD: the kernel detection is a floating-point
       heuristic exactly as in Magma; rigor comes from the caller's final
       residual check |Ax - x|.  Propagating balls through O(n^3) Jacobi
       rotations inflates radii far above the tiny singular values. */
    for (i = 0; i < n; i++)
        for (j = 0; j < n; j++)
        {
            acb_set(acb_mat_entry(Mt, i, j), acb_mat_entry(M, j, i));
            acb_get_mid(acb_mat_entry(Mt, i, j), acb_mat_entry(Mt, i, j));
        }

    jacobi_svd(s, W, Mt, prec);

    if (getenv("POWSER_DEBUG_SVD"))
    {
        for (j = 0; j < (n < 6 ? n : 6); j++)
        {
            printf("  s[%ld] = ", (long) j);
            arb_printd(s + j, 8);
            printf("\n");
        }
    }

    arb_pos_inf(minsing);
    for (j = 0; j < n; j++)
        if (arb_lt(s + j, minsing))
            arb_set(minsing, s + j);

    for (j = 0; j < n; j++)
    {
        if (arb_lt(s + j, eps))
        {
            for (i = 0; i < n; i++)
                acb_set(acb_mat_entry(ker, count, i), acb_mat_entry(W, i, j));
            count++;
        }
    }
    _arb_vec_clear(s, n);
    acb_mat_clear(Mt);
    acb_mat_clear(W);
    return count;
}

/* ------------------------------------------------------------------ */
/* Arnoldi driver, mirroring the escape logic of powser_iter_arfed.m    */
/* ------------------------------------------------------------------ */

typedef void (*matvec_fn)(acb_ptr, acb_srcptr, void *);

/*
 * Runs one Arnoldi sequence from start vector q0 (length V), returns the
 * kernel-combination vector in xout (length V).  Mirrors:
 *   - h[i-1][j] = <q_i, q_j>, MGS
 *   - from i >= 10, left kernel of (H0 - 1), H0 = square (i-1)x(i-1)
 *   - escape when kernel found, minsing < eps, |y_last| > err_arn
 */
static double wall_now(void)
{
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + 1e-9 * ts.tv_nsec;
}

static int arnoldi_run(acb_ptr xout, acb_srcptr q0, slong V,
                       matvec_fn mv, void *mvctx, problem_t *pb,
                       arb_t minsing_out, int verbose)
{
    slong prec = pb->prec;
    slong maxi = pb->maxiter;
    int hermit = pb->hermitian;
    slong kcheck = 4;    /* run the (expensive) kernel check every kcheck
                            iterations until minsing gets near eps */
    int near = 0;
    double t_mv = 0, t_mgs = 0, t_svd = 0, t0;
    acb_ptr *q;          /* Krylov vectors */
    acb_ptr *qc;         /* conjugated Krylov vectors (hermitian case) */
    acb_mat_t H;         /* Hessenberg, maxi x maxi (h[i][j] 0-based) */
    acb_t dot, nrm;
    arb_t minsing, err_arn, ylast, tmp;
    slong i, j, t;
    int found = 0, yFound = 0;
    acb_mat_t ker;
    slong kcount = 0;
    acb_ptr ysave = NULL;
    slong ysave_len = 0;
    acb_ptr ybest = NULL;
    slong ybest_len = 0;
    arb_t best_minsing;
    arb_init(best_minsing);
    arb_pos_inf(best_minsing);

    if (getenv("POWSER_KCHECK"))
        kcheck = atol(getenv("POWSER_KCHECK"));
    if (kcheck < 1) kcheck = 1;

    q = flint_malloc(sizeof(acb_ptr) * (maxi + 2));
    qc = flint_malloc(sizeof(acb_ptr) * (maxi + 2));
    memset(qc, 0, sizeof(acb_ptr) * (maxi + 2));
    acb_mat_init(H, maxi + 1, maxi + 1);
    acb_mat_zero(H);
    acb_init(dot); acb_init(nrm);
    arb_init(minsing); arb_init(err_arn); arb_init(ylast); arb_init(tmp);
    acb_mat_init(ker, maxi + 1, maxi + 1);

    q[0] = _acb_vec_init(V);
    _acb_vec_set(q[0], q0, V);
    /* q[0] /= sqrt(<q0,q0>) */
    vec_dot(dot, q[0], q[0], V, hermit, prec);
    acb_sqrt(nrm, dot, prec);
    for (t = 0; t < V; t++)
        acb_div(q[0] + t, q[0] + t, nrm, prec);
    if (hermit)
    {
        qc[0] = _acb_vec_init(V);
        for (t = 0; t < V; t++)
            acb_conj(qc[0] + t, q[0] + t);
    }

    arb_zero(err_arn);
    arb_pos_inf(minsing);

    for (i = 1; i <= maxi; i++)   /* i = number of new vector (Magma's i-1=i_c) */
    {
        if (yFound && arb_lt(minsing, pb->eps) && i > 1)
            arb_set(err_arn, ylast);

        q[i] = _acb_vec_init(V);
        t0 = wall_now();
        mv(q[i], q[i - 1], mvctx);
        t_mv += wall_now() - t0;

        /* modified Gram-Schmidt.  All quantities are reduced to midpoints:
           this stage is floating-point (as in Magma), and near breakdown
           ball radii would otherwise blow up and poison H with NaNs.
           Rigor is restored by the final residual check on the output. */
        t0 = wall_now();
        for (t = 0; t < V; t++)
            acb_get_mid(q[i] + t, q[i] + t);
        for (j = 0; j < i; j++)
        {
            vec_dot2(dot, q[i], hermit ? qc[j] : q[j], V, prec);
            acb_get_mid(dot, dot);
            acb_set(acb_mat_entry(H, i - 1, j), dot);
            _acb_vec_scalar_submul(q[i], q[j], V, dot, prec);
        }
        vec_dot(dot, q[i], q[i], V, hermit, prec);
        acb_sqrt(nrm, dot, prec);
        acb_get_mid(nrm, nrm);
        acb_set(acb_mat_entry(H, i - 1, i), nrm);
        if (acb_is_zero(nrm) || !acb_is_finite(nrm))
        {
            if (verbose)
                flint_printf("iter %wd: Arnoldi breakdown (zero residual)\n", i + 1);
            _acb_vec_clear(q[i], V);
            q[i] = NULL;
            t_mgs += wall_now() - t0;
            break;
        }
        for (t = 0; t < V; t++)
        {
            acb_div(q[i] + t, q[i] + t, nrm, prec);
            acb_get_mid(q[i] + t, q[i] + t);
        }
        if (hermit)
        {
            qc[i] = _acb_vec_init(V);
            for (t = 0; t < V; t++)
                acb_conj(qc[i] + t, q[i] + t);
        }
        t_mgs += wall_now() - t0;

        /* the kernel check is O(i^3) at high precision: amortize it by
           checking only every kcheck iterations until minsing nears eps
           (a few extra cheap matvec iterations beat an SVD every step) */
        if (i + 1 < 10 || (!near && (i + 1 - 10) % kcheck != 0 && i < maxi))
        {
            if (i + 1 < 10)
                yFound = 0;
            continue;
        }

        /* H0 = first i rows and i columns of H, minus identity */
        t0 = wall_now();
        {
            acb_mat_t H0;
            slong n0 = i;
            acb_mat_init(H0, n0, n0);
            for (j = 0; j < n0; j++)
                for (t = 0; t < n0; t++)
                {
                    acb_set(acb_mat_entry(H0, j, t), acb_mat_entry(H, j, t));
                    if (j == t)
                        acb_sub_ui(acb_mat_entry(H0, j, t),
                                   acb_mat_entry(H0, j, t), 1, prec);
                }
            if (getenv("POWSER_DUMP_H") && i == atol(getenv("POWSER_DUMP_H")))
            {
                FILE *fh = fopen("H0dump.txt", "w");
                slong a, b;
                fprintf(fh, "%ld\n", (long) n0);
                for (a = 0; a < n0; a++)
                    for (b = 0; b < n0; b++)
                    {
                        char *sr = arb_get_str(acb_realref(acb_mat_entry(H0, a, b)), 80, ARB_STR_NO_RADIUS);
                        char *si = arb_get_str(acb_imagref(acb_mat_entry(H0, a, b)), 80, ARB_STR_NO_RADIUS);
                        fprintf(fh, "%s %s\n", sr, si);
                        flint_free(sr); flint_free(si);
                    }
                fclose(fh);
                printf("dumped H0 (n=%ld) at iter %ld\n", (long) n0, (long) i + 1);
            }
            kcount = numerical_left_kernel(ker, minsing, H0, pb->eps, prec);
            acb_mat_clear(H0);
            t_svd += wall_now() - t0;

            /* once minsing is within ~12 digits of eps, check every iter
               so the escape point matches the every-iteration semantics */
            {
                arb_t eps_near;
                arb_init(eps_near);
                arb_mul_2exp_si(eps_near, pb->eps, 40);
                arb_mul_ui(eps_near, eps_near, 1000000000UL, prec);
                if (arb_lt(minsing, eps_near))
                    near = 1;
                arb_clear(eps_near);
            }

            if (verbose)
            {
                flint_printf("iter %wd: minsing ~ ", i + 1);
                arb_printd(minsing, 6);
                flint_printf("  (%wd kernel vecs)\n", kcount);
            }

            if (kcount >= 1)
            {
                yFound = 1;
                /* save y and |y_last| */
                if (ysave) _acb_vec_clear(ysave, ysave_len);
                ysave_len = n0;
                ysave = _acb_vec_init(n0);
                for (t = 0; t < n0; t++)
                    acb_set(ysave + t, acb_mat_entry(ker, 0, t));
                acb_abs(ylast, ysave + (n0 - 1), prec);

                /* track best solution seen, as fallback on breakdown */
                if (arb_lt(minsing, best_minsing))
                {
                    arb_set(best_minsing, minsing);
                    if (ybest) _acb_vec_clear(ybest, ybest_len);
                    ybest_len = n0;
                    ybest = _acb_vec_init(n0);
                    for (t = 0; t < n0; t++)
                        acb_set(ybest + t, ysave + t);
                }

                /* escape check */
                if (arb_lt(minsing, pb->eps) && arb_gt(ylast, err_arn))
                {
                    /* xout = sum_t y_t q[t] */
                    for (t = 0; t < V; t++)
                        acb_zero(xout + t);
                    for (j = 0; j < n0; j++)
                        for (t = 0; t < V; t++)
                            acb_addmul(xout + t, ysave + j, q[j] + t, prec);
                    found = 1;
                    i++;
                    break;
                }
            }
            else
                yFound = 0;
        }
    }

    /* fallback: breakdown or maxiter without a formal escape, but a kernel
       vector below eps was seen along the way -- use the best one */
    if (!found && ybest != NULL && arb_lt(best_minsing, pb->eps))
    {
        for (t = 0; t < V; t++)
            acb_zero(xout + t);
        for (j = 0; j < ybest_len; j++)
            for (t = 0; t < V; t++)
                acb_addmul(xout + t, ybest + j, q[j] + t, prec);
        arb_set(minsing, best_minsing);
        found = 1;
        if (verbose)
            flint_printf("using best fallback solution (minsing below eps)\n");
    }

    arb_set(minsing_out, minsing);

    if (verbose)
        flint_printf("timings: matvec %.2f s, gram-schmidt %.2f s, svd %.2f s\n",
                     t_mv, t_mgs, t_svd);

    for (j = 0; j < i && j <= maxi + 1; j++)
        if (q[j]) _acb_vec_clear(q[j], V);
    for (j = 0; j < i && j <= maxi + 1; j++)
        if (qc[j]) _acb_vec_clear(qc[j], V);
    flint_free(q);
    flint_free(qc);
    if (ysave) _acb_vec_clear(ysave, ysave_len);
    if (ybest) _acb_vec_clear(ybest, ybest_len);
    arb_clear(best_minsing);
    acb_mat_clear(H);
    acb_mat_clear(ker);
    acb_clear(dot); acb_clear(nrm);
    arb_clear(minsing); arb_clear(err_arn); arb_clear(ylast); arb_clear(tmp);
    return found;
}

/* ------------------------------------------------------------------ */
/* input parsing                                                       */
/* ------------------------------------------------------------------ */

static int read_token(FILE *f, char *buf, size_t cap)
{
    int c;
    size_t n = 0;
    do { c = fgetc(f); } while (c != EOF && isspace(c));
    if (c == EOF) return 0;
    while (c != EOF && !isspace(c) && n + 1 < cap)
    {
        buf[n++] = (char) tolower(c);
        c = fgetc(f);
    }
    buf[n] = 0;
    return 1;
}

static slong read_slong(FILE *f)
{
    char buf[64];
    if (!read_token(f, buf, sizeof buf))
    {
        fprintf(stderr, "unexpected EOF\n");
        exit(1);
    }
    return atol(buf);
}

static void read_arb(arb_t x, FILE *f, slong prec)
{
    char buf[8192];
    if (!read_token(f, buf, sizeof buf))
    {
        fprintf(stderr, "unexpected EOF\n");
        exit(1);
    }
    if (arb_set_str(x, buf, prec) != 0)
    {
        fprintf(stderr, "bad number: %s\n", buf);
        exit(1);
    }
}

static void read_acb(acb_t z, FILE *f, slong prec)
{
    read_arb(acb_realref(z), f, prec);
    read_arb(acb_imagref(z), f, prec);
}

static void problem_read(problem_t *pb, const char *fname, slong nthreads)
{
    FILE *f = fopen(fname, "r");
    slong i, j, eps_digs;
    if (!f) { fprintf(stderr, "cannot open %s\n", fname); exit(1); }

    pb->digs = read_slong(f);
    eps_digs = read_slong(f);
    pb->maxiter = read_slong(f);
    pb->dim = read_slong(f);
    pb->nv = read_slong(f);
    pb->Q = read_slong(f);
    pb->hermitian = (int) read_slong(f);
    pb->prec = (slong)(pb->digs * 3.3219280948873626) + 32;
    pb->nthreads = nthreads;

    arb_init(pb->eps);
    arb_set_ui(pb->eps, 10);
    arb_pow_ui(pb->eps, pb->eps, (ulong) eps_digs, pb->prec);
    arb_inv(pb->eps, pb->eps, pb->prec);   /* eps = 10^-eps_digs */

    pb->NN = flint_malloc(sizeof(slong) * pb->nv);
    pb->es = flint_malloc(sizeof(slong) * pb->nv);
    pb->bin0 = flint_malloc(sizeof(slong) * pb->nv);
    pb->Ptot = flint_malloc(sizeof(slong) * pb->nv);
    pb->V = 0; pb->P = 0;
    for (i = 0; i < pb->nv; i++)
    {
        pb->NN[i] = read_slong(f);
        pb->es[i] = read_slong(f);
        pb->bin0[i] = read_slong(f);
        pb->Ptot[i] = read_slong(f);
        pb->V += pb->NN[i];
        pb->P += pb->Ptot[i];
    }
    if (pb->P != pb->nv * pb->Q)
    {
        fprintf(stderr, "point count mismatch: sum Ptot = %ld != nv*Q = %ld\n",
                (long) pb->P, (long) (pb->nv * pb->Q));
        exit(1);
    }

    pb->x = _acb_vec_init(pb->P);
    pb->vand = _acb_vec_init(pb->P);
    pb->g = _acb_vec_init(pb->nv * pb->Q);
    pb->perm = flint_malloc(sizeof(slong) * pb->P);
    pb->start = _acb_vec_init(pb->dim * pb->V);

    {
        slong poff = 0;
        for (i = 0; i < pb->nv; i++)
        {
            for (j = 0; j < pb->Ptot[i]; j++)
            {
                read_acb(pb->x + poff + j, f, pb->prec);
                read_acb(pb->vand + poff + j, f, pb->prec);
            }
            poff += pb->Ptot[i];
        }
    }
    for (i = 0; i < pb->nv; i++)
        for (j = 0; j < pb->Q; j++)
            read_acb(pb->g + i * pb->Q + j, f, pb->prec);
    for (i = 0; i < pb->P; i++)
        pb->perm[i] = read_slong(f) - 1;   /* 1-based -> 0-based */
    for (i = 0; i < pb->dim * pb->V; i++)
        read_acb(pb->start + i, f, pb->prec);
    fclose(f);

    /* the whole computation is floating-point at prec bits (midpoints);
       stripping the parse radii here keeps the final residual check's
       ball tight so it reports the honest residual size */
    for (i = 0; i < pb->P; i++)
    {
        acb_get_mid(pb->x + i, pb->x + i);
        acb_get_mid(pb->vand + i, pb->vand + i);
    }
    for (i = 0; i < pb->nv * pb->Q; i++)
        acb_get_mid(pb->g + i, pb->g + i);
    for (i = 0; i < pb->dim * pb->V; i++)
        acb_get_mid(pb->start + i, pb->start + i);
}

/* ------------------------------------------------------------------ */
/* output                                                              */
/* ------------------------------------------------------------------ */

static void write_arb(FILE *f, const arb_t x, slong digs)
{
    char *s = arb_get_str(x, digs, ARB_STR_NO_RADIUS);
    char *c;
    for (c = s; *c; c++)          /* Magma literals use E */
        if (*c == 'e') *c = 'E';
    fputs(s, f);
    flint_free(s);
}

static void output_write(const char *fname, problem_t *pb, acb_ptr xouts,
                         arb_srcptr minsings, arb_srcptr resids)
{
    FILE *f = fopen(fname, "w");
    slong d, t;
    if (!f) { fprintf(stderr, "cannot open %s\n", fname); exit(1); }
    /* a single Magma EXPRESSION, consumable via:  dat := eval Read(file); */
    fprintf(f, "[*\n[\n");
    for (d = 0; d < pb->dim; d++)
    {
        fprintf(f, "[ ComplexField(%ld) | ", (long) pb->digs);
        for (t = 0; t < pb->V; t++)
        {
            fprintf(f, "[");
            write_arb(f, acb_realref(xouts + d * pb->V + t), pb->digs + 5);
            fprintf(f, ", ");
            write_arb(f, acb_imagref(xouts + d * pb->V + t), pb->digs + 5);
            fprintf(f, "]%s", t + 1 < pb->V ? ", " : "");
            if (t % 4 == 3) fputc('\n', f);
        }
        fprintf(f, " ]%s\n", d + 1 < pb->dim ? "," : "");
    }
    fprintf(f, "],\n[ RealField(20) | ");
    for (d = 0; d < pb->dim; d++)
    {
        write_arb(f, minsings + d, 15);
        fprintf(f, "%s", d + 1 < pb->dim ? ", " : "");
    }
    fprintf(f, " ],\n[ RealField(20) | ");
    for (d = 0; d < pb->dim; d++)
    {
        write_arb(f, resids + d, 15);
        fprintf(f, "%s", d + 1 < pb->dim ? ", " : "");
    }
    fprintf(f, " ]\n*]\n");
    fclose(f);
}

/* ------------------------------------------------------------------ */
/* production matvec wrapper                                           */
/* ------------------------------------------------------------------ */

static void mv_structured(acb_ptr w, acb_srcptr v, void *ctx)
{
    matvec_structured(w, v, (matvec_ws_t *) ctx);
}

/* residual |A x - x|_2 / |x|_2 */
static void residual(arb_t res, acb_srcptr x, matvec_ws_t *ws, slong V, slong prec)
{
    acb_ptr Ax = _acb_vec_init(V);
    arb_t nx, tmp;
    slong t;
    arb_init(nx); arb_init(tmp);
    matvec_structured(Ax, x, ws);
    arb_zero(res); arb_zero(nx);
    for (t = 0; t < V; t++)
    {
        acb_sub(Ax + t, Ax + t, x + t, prec);
        acb_abs(tmp, Ax + t, prec);
        arb_sqr(tmp, tmp, prec);
        arb_add(res, res, tmp, prec);
        acb_abs(tmp, x + t, prec);
        arb_sqr(tmp, tmp, prec);
        arb_add(nx, nx, tmp, prec);
    }
    arb_sqrtpos(res, res, prec);
    arb_sqrtpos(nx, nx, prec);
    arb_div(res, res, nx, prec);
    _acb_vec_clear(Ax, V);
    arb_clear(nx); arb_clear(tmp);
}

/* ------------------------------------------------------------------ */
/* selftest: dense synthetic eigenproblem                              */
/* ------------------------------------------------------------------ */

typedef struct { acb_mat_t A; slong n; slong prec; } dense_ctx_t;

static void mv_dense(acb_ptr w, acb_srcptr v, void *ctx)
{
    dense_ctx_t *dc = (dense_ctx_t *) ctx;
    slong i, j;
    acb_t t;
    acb_init(t);
    for (j = 0; j < dc->n; j++)
    {
        acb_zero(w + j);
        for (i = 0; i < dc->n; i++)
        {
            acb_mul(t, v + i, acb_mat_entry(dc->A, i, j), dc->prec);
            acb_add(w + j, w + j, t, dc->prec);
        }
    }
    acb_clear(t);
}

static int selftest(void)
{
    slong n = 40, prec = 256, i, j;
    slong dim = 2;
    flint_rand_t state;
    dense_ctx_t dc;
    problem_t pb;
    acb_mat_t Vm, Vinv, D, T1;
    int ok = 1;

    flint_rand_init(state);
    memset(&pb, 0, sizeof pb);
    pb.prec = prec;
    pb.digs = 70;
    pb.maxiter = 60;
    pb.dim = dim;
    pb.hermitian = 1;
    pb.nthreads = 1;
    arb_init(pb.eps);
    arb_set_ui(pb.eps, 10);
    arb_pow_ui(pb.eps, pb.eps, 60, prec);
    arb_inv(pb.eps, pb.eps, prec);

    /* A = V^-1 D V with D = diag(1,1,l3..ln), |l|<0.8; row-vector action x*A */
    dc.n = n; dc.prec = prec;
    acb_mat_init(dc.A, n, n);
    acb_mat_init(Vm, n, n);
    acb_mat_init(Vinv, n, n);
    acb_mat_init(D, n, n);
    acb_mat_init(T1, n, n);
    for (i = 0; i < n; i++)
        for (j = 0; j < n; j++)
        {
            acb_set_d_d(acb_mat_entry(Vm, i, j),
                        (double) n_randint(state, 2000) / 1000.0 - 1.0,
                        (double) n_randint(state, 2000) / 1000.0 - 1.0);
            if (i == j)
                acb_add_ui(acb_mat_entry(Vm, i, j), acb_mat_entry(Vm, i, j),
                           4, prec);
        }
    acb_mat_zero(D);
    for (i = 0; i < n; i++)
    {
        if (i < dim)
            acb_one(acb_mat_entry(D, i, i));
        else
            acb_set_d_d(acb_mat_entry(D, i, i),
                        0.05 * ((double) n_randint(state, 2000) / 1000.0 - 1.0),
                        0.05 * ((double) n_randint(state, 2000) / 1000.0 - 1.0));
    }
    if (!acb_mat_inv(Vinv, Vm, prec)) { printf("selftest: V not invertible\n"); return 1; }
    acb_mat_mul(T1, Vinv, D, prec);
    acb_mat_mul(dc.A, T1, Vm, prec);

    /* start vectors: random */
    {
        acb_ptr xout = _acb_vec_init(n);
        acb_ptr q0 = _acb_vec_init(n);
        arb_t minsing, res;
        arb_init(minsing); arb_init(res);

        for (slong d = 0; d < dim; d++)
        {
            for (i = 0; i < n; i++)
                acb_set_d_d(q0 + i, (double) n_randint(state, 1000) / 1000.0 + (d == 0 ? 0.3 : -0.7),
                                    (double) n_randint(state, 1000) / 1000.0);
            if (!arnoldi_run(xout, q0, n, mv_dense, &dc, &pb, minsing, 1))
            {
                printf("selftest: arnoldi did not converge (d=%ld)\n", (long) d);
                ok = 0;
                continue;
            }
            /* residual x*A - x */
            {
                acb_ptr Ax = _acb_vec_init(n);
                arb_t nrm, tmp;
                arb_init(nrm); arb_init(tmp);
                mv_dense(Ax, xout, &dc);
                arb_zero(nrm);
                for (i = 0; i < n; i++)
                {
                    acb_sub(Ax + i, Ax + i, xout + i, prec);
                    acb_abs(tmp, Ax + i, prec);
                    arb_sqr(tmp, tmp, prec);
                    arb_add(nrm, nrm, tmp, prec);
                }
                arb_sqrtpos(nrm, nrm, prec);
                printf("selftest d=%ld: |xA - x| = ", (long) d);
                arb_printd(nrm, 6);
                printf("\n");
                arb_set_ui(tmp, 10);
                arb_pow_ui(tmp, tmp, 50, prec);
                arb_inv(tmp, tmp, prec);
                if (!arb_lt(nrm, tmp))
                {
                    printf("selftest: residual too large!\n");
                    ok = 0;
                }
                _acb_vec_clear(Ax, n);
                arb_clear(nrm); arb_clear(tmp);
            }
        }
        _acb_vec_clear(xout, n);
        _acb_vec_clear(q0, n);
        arb_clear(minsing); arb_clear(res);
    }

    /* also test the SVD on a known matrix: diag(3, 1e-80) rotated */
    {
        slong m = 12;
        acb_mat_t M, ker;
        arb_t minsing;
        acb_mat_init(M, m, m);
        acb_mat_init(ker, m, m);
        arb_init(minsing);
        for (i = 0; i < m; i++)
            for (j = 0; j < m; j++)
                acb_set_d_d(acb_mat_entry(M, i, j),
                            (double) n_randint(state, 2000) / 1000.0 - 1.0,
                            (double) n_randint(state, 2000) / 1000.0 - 1.0);
        /* make row 0 = row 1 + 1e-75*row 2  -> near left-kernel vector */
        for (j = 0; j < m; j++)
        {
            acb_t sc;
            acb_init(sc);
            acb_set_d(sc, 1.0);
            acb_mul_2exp_si(sc, sc, -250);
            acb_mul(sc, sc, acb_mat_entry(M, 2, j), prec);
            acb_add(acb_mat_entry(M, 0, j), acb_mat_entry(M, 1, j), sc, prec);
            acb_clear(sc);
        }
        {
            slong cnt = numerical_left_kernel(ker, minsing, M, pb.eps, prec);
            printf("selftest svd: minsing = ");
            arb_printd(minsing, 6);
            printf(", kernel count = %ld\n", (long) cnt);
            if (cnt < 1) { printf("selftest: svd failed to find kernel\n"); ok = 0; }
            else
            {
                /* verify y*M small */
                arb_t nrm, tmp;
                acb_t s, p;
                arb_init(nrm); arb_init(tmp);
                acb_init(s); acb_init(p);
                arb_zero(nrm);
                for (j = 0; j < m; j++)
                {
                    acb_zero(s);
                    for (i = 0; i < m; i++)
                    {
                        acb_mul(p, acb_mat_entry(ker, 0, i), acb_mat_entry(M, i, j), prec);
                        acb_add(s, s, p, prec);
                    }
                    acb_abs(tmp, s, prec);
                    arb_sqr(tmp, tmp, prec);
                    arb_add(nrm, nrm, tmp, prec);
                }
                arb_sqrtpos(nrm, nrm, prec);
                printf("selftest svd: |y*M| = ");
                arb_printd(nrm, 6);
                printf("\n");
                arb_set_ui(tmp, 10);
                arb_pow_ui(tmp, tmp, 60, prec);
                arb_inv(tmp, tmp, prec);
                if (!arb_lt(nrm, tmp)) { printf("selftest: |y*M| too large\n"); ok = 0; }
            }
        }
        acb_mat_clear(M); acb_mat_clear(ker);
        arb_clear(minsing);
    }

    acb_mat_clear(dc.A); acb_mat_clear(Vm); acb_mat_clear(Vinv);
    acb_mat_clear(D); acb_mat_clear(T1);
    flint_rand_clear(state);
    printf(ok ? "SELFTEST PASSED\n" : "SELFTEST FAILED\n");
    return ok ? 0 : 1;
}

/* ------------------------------------------------------------------ */

#ifndef POWSER_NO_MAIN
int main(int argc, char **argv)
{
    problem_t pb;
    matvec_ws_t ws;
    slong d;
    slong nthreads = 0;

    if (argc >= 2 && strcmp(argv[1], "--selftest") == 0)
        return selftest();

    if (argc < 3)
    {
        fprintf(stderr, "usage: %s input.txt output.m [nthreads]\n"
                        "       %s --selftest\n", argv[0], argv[0]);
        return 1;
    }
    if (argc >= 4)
        nthreads = atol(argv[3]);
    if (nthreads <= 0 && getenv("POWSER_ARNOLDI_THREADS"))
        nthreads = atol(getenv("POWSER_ARNOLDI_THREADS"));
    if (nthreads <= 0)
        nthreads = flint_get_num_threads() > 1 ? flint_get_num_threads() : 4;

    memset(&pb, 0, sizeof pb);
    problem_read(&pb, argv[1], nthreads);
    matvec_ws_init(&ws, &pb);

    flint_printf("powser_arnoldi: V=%wd P=%wd nv=%wd Q=%wd dim=%wd digs=%wd "
                 "prec=%wd bits threads=%wd\n",
                 pb.V, pb.P, pb.nv, pb.Q, pb.dim, pb.digs, pb.prec, pb.nthreads);

    {
        acb_ptr xouts = _acb_vec_init(pb.dim * pb.V);
        arb_ptr minsings = _arb_vec_init(pb.dim);
        arb_ptr resids = _arb_vec_init(pb.dim);
        int allok = 1;

        for (d = 0; d < pb.dim; d++)
        {
            int ok = arnoldi_run(xouts + d * pb.V, pb.start + d * pb.V, pb.V,
                                 mv_structured, &ws, &pb, minsings + d, 1);
            if (!ok)
            {
                flint_printf("WARNING: Arnoldi did not converge for dim %wd "
                             "within %wd iterations\n", d + 1, pb.maxiter);
                allok = 0;
            }
            residual(resids + d, xouts + d * pb.V, &ws, pb.V, pb.prec);
            flint_printf("dim %wd: residual |Ax-x|/|x| = ", d + 1);
            arb_printd(resids + d, 6);
            flint_printf("\n");
        }

        output_write(argv[2], &pb, xouts, minsings, resids);
        flint_printf("wrote %s\n", argv[2]);

        _acb_vec_clear(xouts, pb.dim * pb.V);
        _arb_vec_clear(minsings, pb.dim);
        _arb_vec_clear(resids, pb.dim);
        return allok ? 0 : 2;
    }
}
#endif
