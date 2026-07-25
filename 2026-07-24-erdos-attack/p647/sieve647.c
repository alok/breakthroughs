/*
 * sieve647.c -- direct exhaustive sweep for Erdos problem #647 witnesses.
 *
 * Condition: n is a "solution" iff  max_{m<n} (m + tau(m)) <= n + 2.
 * Known solutions: n in {1..6, 8, 10, 12, 24} (tiny) -- witness needs n > 24.
 *
 * Method: segmented sieve computing exact tau(m) for every m via
 * smallest-prime-factor style marking:
 *   - p = 2 handled by ctz at init
 *   - odd primes p <= sqrt(R): level-1 marking (multiples of p): exact
 *     division via multiplication by p^{-1} mod 2^64; level-2 (multiples
 *     of p^2): full exponent extraction (rare, density 1/p^2)
 *   - after all primes <= sqrt(R) removed, remaining cofactor is 1 or a
 *     single prime > sqrt(R) (cannot be composite: product of two primes
 *     > sqrt(R) would exceed R > m)
 *
 * Parallel two-pass scheme:
 *   Pass 1 (parallel over blocks): compute per-block max(m + tau(m)),
 *     argmax, and record "locally feasible" candidates n where the
 *     in-block prefix max over m < n is <= n + 2 (a superset of true
 *     solutions; every block start is trivially recorded).
 *   Pass 2 (sequential, trivial): prefix-max across blocks; candidate n is
 *     a true solution iff max(incoming_prefix_max, internal_prefix) <= n+2.
 *
 * Warm start: for a scan of [S, E), sieving begins at W0 = (S <= 10^7 ? 1 :
 * S - 10^7). Any m < W0 satisfies m + tau(m) <= m + 2*sqrt(m)
 * < (S - 10^7) + 2*sqrt(8e12) < S <= n + 2 for all n >= S (tau(m) <= 2*sqrt(m)
 * since divisors pair below/above sqrt(m)); such m can never violate the
 * condition for n >= S, so the warm-up window is rigorously sufficient
 * for E <= 8e12 (2*sqrt(8e12) < 5.7e6 < 1e7).
 *
 * Usage: sieve647 S E [threads] [--dump]
 *   scans n in [S, E); --dump prints "m tau(m)" for all m (small ranges).
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <inttypes.h>
#include <pthread.h>
#include <stdatomic.h>
#include <math.h>
#include <time.h>

#ifndef BLOCK_LOG
#define BLOCK_LOG 21
#endif
#define BLOCK ((uint64_t)1 << BLOCK_LOG)
#define WARMUP ((uint64_t)10000000)

typedef struct { uint64_t n; uint64_t internal_max; } cand_t;

typedef struct {
    cand_t *c; size_t len, cap;
    uint64_t elems_done;
} tstate_t;

static uint64_t W0, S, E, NB;
static int NTHREADS, DUMP;
static uint64_t *P, *INV, *LIM;   /* odd primes <= sqrt(E-1), inverses mod 2^64, UINT64_MAX/p */
static uint32_t NP;
static uint64_t *blockmax, *blockargmax;
static tstate_t *tstates;
static atomic_uint_fast64_t next_block, done_blocks;
static double t_start;

static double now(void) {
    struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + 1e-9 * ts.tv_nsec;
}

static uint64_t isqrt64(uint64_t x) {
    uint64_t r = (uint64_t)sqrtl((long double)x);
    while (r > 0 && r * r > x) r--;
    while ((r + 1) * (r + 1) <= x) r++;
    return r;
}

/* inverse of odd p mod 2^64 (Newton iteration) */
static uint64_t inv64(uint64_t p) {
    uint64_t x = p;               /* correct mod 2^4 */
    for (int i = 0; i < 5; i++) x *= 2 - p * x;
    return x;
}

static void build_primes(uint64_t limit) {
    uint64_t n = limit + 1;
    uint8_t *comp = calloc(n, 1);
    if (!comp) { fprintf(stderr, "OOM primes\n"); exit(1); }
    for (uint64_t i = 3; i * i <= limit; i += 2)
        if (!comp[i])
            for (uint64_t j = i * i; j <= limit; j += 2 * i) comp[j] = 1;
    uint32_t cnt = 0;
    for (uint64_t i = 3; i <= limit; i += 2) if (!comp[i]) cnt++;
    P = malloc((size_t)cnt * 8); INV = malloc((size_t)cnt * 8); LIM = malloc((size_t)cnt * 8);
    if (!P || !INV || !LIM) { fprintf(stderr, "OOM prime tables\n"); exit(1); }
    NP = 0;
    for (uint64_t i = 3; i <= limit; i += 2)
        if (!comp[i]) {
            P[NP] = i; INV[NP] = inv64(i); LIM[NP] = UINT64_MAX / i; NP++;
        }
    free(comp);
}

static void cand_push(tstate_t *t, uint64_t n, uint64_t im) {
    if (t->len == t->cap) {
        t->cap = t->cap ? t->cap * 2 : 4096;
        t->c = realloc(t->c, t->cap * sizeof(cand_t));
        if (!t->c) { fprintf(stderr, "OOM cands\n"); exit(1); }
    }
    t->c[t->len].n = n; t->c[t->len].internal_max = im; t->len++;
}

static void *worker(void *arg) {
    tstate_t *ts = arg;
    uint64_t *rem = malloc(BLOCK * 8);
    uint16_t *tau = malloc(BLOCK * 2);
    if (!rem || !tau) { fprintf(stderr, "OOM block\n"); exit(1); }

    for (;;) {
        uint64_t b = atomic_fetch_add(&next_block, 1);
        if (b >= NB) break;
        uint64_t L = W0 + b * BLOCK;
        uint64_t len = BLOCK; if (L + len > E) len = E - L;
        uint64_t R = L + len;

        /* init: strip factors of 2 */
        for (uint64_t i = 0; i < len; i++) {
            uint64_t m = L + i;
            unsigned e2 = (unsigned)__builtin_ctzll(m);
            rem[i] = m >> e2;
            tau[i] = (uint16_t)(e2 + 1);
        }

        uint64_t sq = isqrt64(R - 1);
        for (uint32_t k = 0; k < NP; k++) {
            uint64_t p = P[k];
            if (p > sq) break;
            uint64_t inv = INV[k], lim = LIM[k];
            /* level 1: divide out one factor of p, tau *= 2 */
            uint64_t st = ((L + p - 1) / p) * p;
            for (uint64_t i = st - L; i < len; i += p) {
                rem[i] *= inv;          /* exact: p | rem[i] here */
                tau[i] = (uint16_t)(tau[i] << 1);
            }
            /* level 2: full exponent for multiples of p^2 (rare) */
            uint64_t pp = p * p;
            if (pp < R) {
                uint64_t st2 = ((L + pp - 1) / pp) * pp;
                for (uint64_t i = st2 - L; i < len; i += pp) {
                    uint64_t r = rem[i] * inv;   /* second division, exact */
                    uint32_t e = 2;
                    for (;;) {
                        uint64_t q = r * inv;
                        if (q > lim) break;      /* not divisible */
                        r = q; e++;
                    }
                    rem[i] = r;
                    tau[i] = (uint16_t)((tau[i] >> 1) * (e + 1));
                }
            }
        }

        /* final pass: tau(m) = tau[i] * (rem>1 ? 2 : 1); track max + candidates */
        uint64_t runmax = 0, argmax = 0;
        for (uint64_t i = 0; i < len; i++) {
            uint64_t m = L + i;
            uint32_t t = tau[i];
            if (rem[i] > 1) t <<= 1;   /* single prime cofactor > sqrt(R) */
            if (DUMP && m >= S) printf("%" PRIu64 " %u\n", m, t);
            if (m >= S && runmax <= m + 2)
                cand_push(ts, m, runmax);
            uint64_t v = m + t;
            if (v > runmax) { runmax = v; argmax = m; }
        }
        blockmax[b] = runmax;
        blockargmax[b] = argmax;
        ts->elems_done += len;

        uint64_t d = atomic_fetch_add(&done_blocks, 1) + 1;
        if ((d & 8191) == 0) {
            double el = now() - t_start;
            double frac = (double)d / (double)NB;
            fprintf(stderr, "[progress] %" PRIu64 "/%" PRIu64 " blocks (%.1f%%) elapsed %.0fs rate %.2fe9/s ETA %.0fs\n",
                    d, NB, 100.0 * frac, el,
                    ((double)d * BLOCK) / el / 1e9, el * (1 - frac) / frac);
            fflush(stderr);
        }
    }
    free(rem); free(tau);
    return NULL;
}

static int cand_cmp(const void *a, const void *b) {
    uint64_t x = ((const cand_t *)a)->n, y = ((const cand_t *)b)->n;
    return x < y ? -1 : x > y ? 1 : 0;
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: %s S E [threads] [--dump]\n", argv[0]); return 2; }
    S = strtoull(argv[1], 0, 10);
    E = strtoull(argv[2], 0, 10);
    NTHREADS = argc > 3 ? atoi(argv[3]) : 16;
    DUMP = (argc > 4 && !strcmp(argv[4], "--dump"));
    if (S < 1) S = 1;
    if (E <= S) { fprintf(stderr, "empty range\n"); return 2; }
    if (E > (uint64_t)8e12) { fprintf(stderr, "E too large for warmup bound proof\n"); return 2; }

    W0 = (S <= WARMUP + 1) ? 1 : S - WARMUP;
    NB = (E - W0 + BLOCK - 1) / BLOCK;

    fprintf(stderr, "scan n in [%" PRIu64 ", %" PRIu64 "), sieve from W0=%" PRIu64 ", %" PRIu64 " blocks of %" PRIu64 ", %d threads\n",
            S, E, W0, NB, BLOCK, NTHREADS);

    build_primes(isqrt64(E - 1) + 1);
    fprintf(stderr, "primes: %u odd primes <= %" PRIu64 "\n", NP, isqrt64(E - 1) + 1);

    blockmax = malloc(NB * 8);
    blockargmax = malloc(NB * 8);
    tstates = calloc(NTHREADS, sizeof(tstate_t));
    if (!blockmax || !blockargmax || !tstates) { fprintf(stderr, "OOM\n"); return 1; }

    atomic_store(&next_block, 0);
    atomic_store(&done_blocks, 0);
    t_start = now();

    pthread_t th[256];
    for (int i = 0; i < NTHREADS; i++) pthread_create(&th[i], 0, worker, &tstates[i]);
    for (int i = 0; i < NTHREADS; i++) pthread_join(th[i], 0);

    double el = now() - t_start;
    uint64_t total_elems = 0; size_t ncand = 0;
    for (int i = 0; i < NTHREADS; i++) { total_elems += tstates[i].elems_done; ncand += tstates[i].len; }
    fprintf(stderr, "pass1 done: %.1fs, %.3fe9 elems/s, %zu candidates\n",
            el, total_elems / el / 1e9, ncand);

    /* merge + sort candidates */
    cand_t *cands = malloc((ncand ? ncand : 1) * sizeof(cand_t));
    if (!cands) { fprintf(stderr, "OOM merge\n"); return 1; }
    size_t off = 0;
    for (int i = 0; i < NTHREADS; i++) {
        memcpy(cands + off, tstates[i].c, tstates[i].len * sizeof(cand_t));
        off += tstates[i].len;
        free(tstates[i].c);
    }
    qsort(cands, ncand, sizeof(cand_t), cand_cmp);

    /* pass 2: sequential prefix max + candidate resolution */
    uint64_t incoming = 0;
    size_t ci = 0;
    int nwitness = 0;
    uint64_t globmax = 0, globargmax = 0;
    /* near-miss tracking: smallest excess = R(n) - (n+2) over candidates */
    #define NNEAR 8
    uint64_t near_excess[NNEAR], near_n[NNEAR];
    for (int i = 0; i < NNEAR; i++) { near_excess[i] = UINT64_MAX; near_n[i] = 0; }

    for (uint64_t b = 0; b < NB; b++) {
        uint64_t Lb = W0 + b * BLOCK;
        uint64_t Rb = Lb + BLOCK; if (Rb > E) Rb = E;
        while (ci < ncand && cands[ci].n < Rb) {
            cand_t *c = &cands[ci++];
            uint64_t total = incoming > c->internal_max ? incoming : c->internal_max;
            if (total <= c->n + 2) {
                if (c->n > 24) {
                    printf("WITNESS n=%" PRIu64 "  R(n)=%" PRIu64 "  n+2=%" PRIu64 "\n",
                           c->n, total, c->n + 2);
                    nwitness++;
                } else {
                    printf("small solution n=%" PRIu64 "  R(n)=%" PRIu64 " <= n+2=%" PRIu64 "%s\n",
                           c->n, total, c->n + 2, total == c->n + 2 ? " (equality)" : "");
                }
            } else {
                uint64_t ex = total - (c->n + 2);
                int worst = 0;
                for (int i = 1; i < NNEAR; i++) if (near_excess[i] > near_excess[worst]) worst = i;
                if (ex < near_excess[worst]) { near_excess[worst] = ex; near_n[worst] = c->n; }
            }
        }
        if (blockmax[b] > incoming) { incoming = blockmax[b]; }
        if (blockmax[b] > globmax) { globmax = blockmax[b]; globargmax = blockargmax[b]; }
    }

    /* sort near list by excess for printing */
    for (int i = 0; i < NNEAR; i++)
        for (int j = i + 1; j < NNEAR; j++)
            if (near_excess[j] < near_excess[i]) {
                uint64_t t1 = near_excess[i]; near_excess[i] = near_excess[j]; near_excess[j] = t1;
                t1 = near_n[i]; near_n[i] = near_n[j]; near_n[j] = t1;
            }

    printf("# range [%" PRIu64 ", %" PRIu64 "): witnesses(n>24)=%d\n", S, E, nwitness);
    printf("# global max m+tau(m) = %" PRIu64 " at m=%" PRIu64 " (tau=%" PRIu64 ")\n",
           globmax, globargmax, globmax - globargmax);
    printf("# candidates examined: %zu\n", ncand);
    printf("# nearest misses among locally-feasible n (excess = R(n)-(n+2)):\n");
    for (int i = 0; i < NNEAR && near_excess[i] != UINT64_MAX; i++)
        printf("#   n=%" PRIu64 "  excess=%" PRIu64 "\n", near_n[i], near_excess[i]);
    printf("# elapsed %.1fs, throughput %.3fe9 elems/s\n", el, total_elems / el / 1e9);
    fflush(stdout);
    return nwitness > 0 ? 42 : 0;
}
