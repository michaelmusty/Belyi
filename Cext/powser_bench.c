/*
 * powser_bench.c — benchmark the core numerical operations of
 * PowerSeriesBasis (Belyi/Code/powser_iter_arfed.m) reimplemented in C
 * with FLINT 3 (acb arithmetic).
 *
 * Per Arnoldi iteration the Magma code does, for each center i = 1..nv:
 *   (1) u_i = q_i * Wp_i      -- Vandermonde matvec = polynomial evaluation
 *                                of coeffs q_i at Q reduced points wp_m
 *   (2) permute/scatter u across centers
 *   (3) v_i = u_i * J_i       -- J[m][n] = jaut_m * zeta_Q^{-n m}
 *                                = pointwise mult + length-Q DFT
 *   (4) modified Gram-Schmidt against previous Krylov vectors
 *   (5) NumericalKernel_old(H-1) -- SVD of small Hessenberg (amortizable)
 *
 * We benchmark (1) and (3) both as DENSE matvecs (what Magma effectively
 * does) and STRUCTURED (Horner evaluation + acb_dft), plus the MGS step.
 *
 * Build: gcc -O2 -fopenmp powser_bench.c -o powser_bench -lflint -lmpfr -lgmp -lm
 * Usage: ./powser_bench [N] [Q] [nv] [prec_decimal] [arn_iter]
 */

#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <time.h>
#include <flint/flint.h>
#include <flint/acb.h>
#include <flint/acb_mat.h>
#include <flint/acb_dft.h>
#ifdef _OPENMP
#include <omp.h>
#endif

static double now_wall(void)
{
#ifdef _OPENMP
    return omp_get_wtime();
#else
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + 1e-9 * ts.tv_nsec;
#endif
}

/* evaluate p(x) = sum_{r<NN} c_r x^r by Horner at one point */
static void horner_eval(acb_t res, acb_srcptr c, slong NN, const acb_t x, slong prec)
{
    slong r;
    acb_set(res, c + (NN - 1));
    for (r = NN - 2; r >= 0; r--)
    {
        acb_mul(res, res, x, prec);
        acb_add(res, res, c + r, prec);
    }
}

int main(int argc, char **argv)
{
    slong N    = (argc > 1) ? atol(argv[1]) : 1168;  /* series degree */
    slong Q    = (argc > 2) ? atol(argv[2]) : 1200;  /* points per center */
    slong nv   = (argc > 3) ? atol(argv[3]) : 2;     /* number of centers */
    slong digs = (argc > 4) ? atol(argv[4]) : 100;   /* decimal digits */
    slong arn  = (argc > 5) ? atol(argv[5]) : 71;    /* Arnoldi iterations (for extrapolation) */
    slong prec = (slong)(digs * 3.3219280948873626) + 16;
    slong NN   = N;                                  /* coeffs per center (~N/e_i in real runs) */
    slong i, m, r, n;

    int nthreads = 1;
#ifdef _OPENMP
    nthreads = omp_get_max_threads();
#endif
    flint_printf("N=%wd Q=%wd nv=%wd prec=%wd bits (%wd digits) threads=%d\n",
                 N, Q, nv, prec, digs, nthreads);

    flint_rand_t state;
    flint_randinit(state);

    /* ---- synthetic data: reduced points wp_m in |w|<0.9, weights jaut_m on unit circle ---- */
    acb_ptr wp   = _acb_vec_init(Q);
    acb_ptr jaut = _acb_vec_init(Q);
    for (m = 0; m < Q; m++)
    {
        double th = 2 * 3.14159265358979323846 * (double) n_randint(state, 1u << 30) / (double)(1u << 30);
        double rad = 0.9 * sqrt((double) n_randint(state, 1u << 30) / (double)(1u << 30));
        acb_set_d_d(wp + m, rad * cos(th), rad * sin(th));
        acb_set_d_d(jaut + m, cos(3 * th), sin(3 * th));
    }

    /* coefficient vector q (one center's block) and full Krylov-length vector */
    acb_ptr q = _acb_vec_init(NN);
    for (r = 0; r < NN; r++)
        acb_set_d_d(q + r, pow(0.97, (double) r) * cos(0.1 * (double) r),
                           pow(0.97, (double) r) * sin(0.17 * (double) r));

    /* =========================== DENSE PATH =========================== */
    /* Wp is NN x Q: Wp[r][m] = wp_m^r  (prefactors folded in; same cost) */
    acb_mat_t Wp, Jm, qrow, urow, vrow;
    acb_mat_init(Wp, NN, Q);
    for (m = 0; m < Q; m++)
    {
        acb_one(acb_mat_entry(Wp, 0, m));
        for (r = 1; r < NN; r++)
            acb_mul(acb_mat_entry(Wp, r, m), acb_mat_entry(Wp, r - 1, m), wp + m, prec);
    }
    /* J is Q x NN: J[m][n] = jaut_m * zeta_Q^{-nm} */
    acb_mat_init(Jm, Q, NN);
    {
        acb_t z, zm;
        acb_init(z); acb_init(zm);
        for (m = 0; m < Q; m++)
        {
            /* zeta_Q^{-m} */
            acb_set_si(z, -m);
            acb_div_si(z, z, Q, prec);
            acb_exp_pi_i(zm, z, prec); /* e^{-2 pi i m / Q}? exp_pi_i(x)=e^{i pi x}; need 2x */
            acb_mul(zm, zm, zm, prec);
            acb_set(acb_mat_entry(Jm, m, 0), jaut + m);
            for (n = 1; n < NN; n++)
                acb_mul(acb_mat_entry(Jm, m, n), acb_mat_entry(Jm, m, n - 1), zm, prec);
        }
        acb_clear(z); acb_clear(zm);
    }
    acb_mat_init(qrow, 1, NN);
    acb_mat_init(urow, 1, Q);
    acb_mat_init(vrow, 1, NN);
    for (r = 0; r < NN; r++) acb_set(acb_mat_entry(qrow, 0, r), q + r);

    double t0, t_dense_wp, t_dense_j;
    t0 = now_wall();
    acb_mat_approx_mul(urow, qrow, Wp, prec);
    t_dense_wp = now_wall() - t0;

    t0 = now_wall();
    acb_mat_approx_mul(vrow, urow, Jm, prec);
    t_dense_j = now_wall() - t0;

    flint_printf("dense  q*Wp   (1x%wd)*(%wdx%wd): %.3f s\n", NN, NN, Q, t_dense_wp);
    flint_printf("dense  u*J    (1x%wd)*(%wdx%wd): %.3f s\n", Q, Q, NN, t_dense_j);

    /* ========================= STRUCTURED PATH ========================= */
    /* (1) polynomial evaluation at Q points, parallel Horner */
    acb_ptr u = _acb_vec_init(Q);
    double t_horner;
    t0 = now_wall();
#ifdef _OPENMP
#pragma omp parallel for schedule(static)
#endif
    for (m = 0; m < Q; m++)
        horner_eval(u + m, q, NN, wp + m, prec);
    t_horner = now_wall() - t0;
    flint_printf("struct q*Wp   Horner at %wd points:  %.3f s\n", Q, t_horner);

    /* (3) pointwise mult + DFT of length Q, keep first NN outputs */
    acb_ptr uw = _acb_vec_init(Q);
    acb_ptr v  = _acb_vec_init(Q);
    double t_dft;
    t0 = now_wall();
    for (m = 0; m < Q; m++)
        acb_mul(uw + m, u + m, jaut + m, prec);
    acb_dft(v, uw, Q, prec);
    t_dft = now_wall() - t0;
    flint_printf("struct u*J    mult + acb_dft(%wd):    %.3f s\n", Q, t_dft);

    /* sanity: structured (1) vs dense (1) agree */
    {
        acb_t diff; acb_init(diff);
        double maxerr = 0;
        for (m = 0; m < Q; m++)
        {
            acb_sub(diff, u + m, acb_mat_entry(urow, 0, m), prec);
            double e = fabs(arf_get_d(arb_midref(acb_realref(diff)), ARF_RND_NEAR))
                     + fabs(arf_get_d(arb_midref(acb_imagref(diff)), ARF_RND_NEAR));
            if (e > maxerr) maxerr = e;
        }
        flint_printf("check  dense vs Horner max abs diff: %.2e\n", maxerr);
        /* sanity: dense J column vs DFT output */
        acb_t s; acb_init(s);
        maxerr = 0;
        for (n = 0; n < 5; n++)
        {
            acb_zero(s);
            for (m = 0; m < Q; m++)
                acb_addmul(s, acb_mat_entry(Jm, m, n), u + m, prec);
            acb_sub(diff, s, v + n, prec);
            double e = fabs(arf_get_d(arb_midref(acb_realref(diff)), ARF_RND_NEAR))
                     + fabs(arf_get_d(arb_midref(acb_imagref(diff)), ARF_RND_NEAR));
            if (e > maxerr) maxerr = e;
        }
        flint_printf("check  dense J vs DFT (first 5 cols) max abs diff: %.2e\n", maxerr);
        acb_clear(s); acb_clear(diff);
    }

    /* ==================== MODIFIED GRAM-SCHMIDT STEP ==================== */
    /* cost model at iteration i: i dot products + i axpys on vectors of
       length nv*Q; we time one dot+axpy pair and scale */
    slong L = nv * Q;
    acb_ptr big1 = _acb_vec_init(L), big2 = _acb_vec_init(L);
    for (m = 0; m < L; m++)
    {
        acb_set_d_d(big1 + m, cos(0.01 * (double) m), sin(0.02 * (double) m));
        acb_set_d_d(big2 + m, cos(0.03 * (double) m), sin(0.01 * (double) m));
    }
    acb_t dot;
    acb_init(dot);
    double t_dot;
    t0 = now_wall();
    for (i = 0; i < 10; i++)
    {
        acb_dot(dot, NULL, 1, big1, 1, big2, 1, L, prec);       /* inner product */
        _acb_vec_scalar_addmul(big1, big2, L, dot, prec);        /* axpy */
    }
    t_dot = (now_wall() - t0) / 10.0;
    flint_printf("MGS    one dot+axpy of length %wd:   %.4f s\n", L, t_dot);

    /* ========================== EXTRAPOLATION ========================== */
    double per_iter_dense  = nv * (t_dense_wp + t_dense_j);
    double per_iter_struct = nv * (t_horner + t_dft);
    double mgs_total_dense = 0, mgs_avg;
    for (i = 1; i <= arn; i++) mgs_total_dense += i * t_dot;
    mgs_avg = mgs_total_dense / arn;

    flint_printf("\n--- per Arnoldi iteration (nv=%wd centers) ---\n", nv);
    flint_printf("dense matvec:      %.3f s\n", per_iter_dense);
    flint_printf("structured matvec: %.3f s\n", per_iter_struct);
    flint_printf("MGS (avg over %wd iters): %.3f s\n", arn, mgs_avg);
    flint_printf("\n--- full run estimate: dim=2 x %wd iterations ---\n", arn);
    flint_printf("dense:      %.1f s\n", 2 * arn * (per_iter_dense + mgs_avg));
    flint_printf("structured: %.1f s\n", 2 * arn * (per_iter_struct + mgs_avg));

    _acb_vec_clear(wp, Q); _acb_vec_clear(jaut, Q); _acb_vec_clear(q, NN);
    _acb_vec_clear(u, Q); _acb_vec_clear(uw, Q); _acb_vec_clear(v, Q);
    _acb_vec_clear(big1, L); _acb_vec_clear(big2, L);
    acb_clear(dot);
    acb_mat_clear(Wp); acb_mat_clear(Jm);
    acb_mat_clear(qrow); acb_mat_clear(urow); acb_mat_clear(vrow);
    flint_randclear(state);
    return 0;
}
