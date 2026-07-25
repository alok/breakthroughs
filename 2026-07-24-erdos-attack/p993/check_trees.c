/* check_trees.c — read gentreeg -p -q parent arrays from stdin, compute
 * independence polynomial by rooted-tree DP (exact uint64, overflow-guarded),
 * check unimodality (and log-concavity), track minimal unimodality margin.
 *
 * Usage: gentreeg -p -q N [res/mod] | ./check_trees N
 *
 * Format: one tree per line, N space-separated ints, 1-indexed vertices,
 * parent[1]=0, parent[i]<i for i>=2.
 *
 * DP: A(v) = x * prod_c B(c)   (v in the independent set)
 *     B(v) = prod_c (A(c)+B(c)) (v not in the set)
 *     I = A(root)+B(root)
 * Coefficients count independent sets => bounded by total #independent sets
 * <= 2^N + tiny, far below 2^63 for N<=40. We still guard multiplies.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define MAXN 64

typedef unsigned long long u64;
typedef __uint128_t u128;

static int N;
static u64 A[MAXN + 1][MAXN + 2], B[MAXN + 1][MAXN + 2];
static int lenA[MAXN + 1], lenB[MAXN + 1]; /* number of coefficients */
static int parent[MAXN + 1];

static u64 trees_checked = 0;
static u64 nonlogconcave_count = 0;
static long long min_margin = 0x7fffffffffffffffLL; /* min over trees of margin */
static char min_margin_tree[512];
static char first_nlc_tree[512];
static u64 violations = 0;

static void die(const char *msg) { fprintf(stderr, "FATAL: %s\n", msg); exit(2); }

/* dst = dst * src, exact convolution with overflow guard */
static void polymul(u64 *dst, int *dlen, const u64 *src, int slen) {
    static u64 tmp[2 * MAXN + 4];
    int n = *dlen + slen - 1;
    memset(tmp, 0, sizeof(u64) * (size_t)n);
    for (int i = 0; i < *dlen; i++) {
        if (!dst[i]) continue;
        for (int j = 0; j < slen; j++) {
            if (!src[j]) continue;
            u128 p = (u128)dst[i] * src[j] + tmp[i + j];
            if (p > 0xFFFFFFFFFFFFFFFFULL) die("overflow in polymul");
            tmp[i + j] = (u64)p;
        }
    }
    memcpy(dst, tmp, sizeof(u64) * (size_t)n);
    *dlen = n;
}

static void report_tree(char *buf, size_t bufsz) {
    size_t off = 0;
    for (int i = 1; i <= N; i++) {
        off += (size_t)snprintf(buf + off, bufsz - off, "%d ", parent[i]);
        if (off >= bufsz - 16) break;
    }
}

int main(int argc, char **argv) {
    if (argc < 2) die("usage: check_trees N [-c]");
    N = atoi(argv[1]);
    if (N < 1 || N > MAXN) die("bad N");
    int dump_coefs = (argc > 2 && strcmp(argv[2], "-c") == 0);

    char line[4096];
    static u64 coef[MAXN + 2];

    while (fgets(line, sizeof line, stdin)) {
        /* parse parents */
        char *p = line;
        int cnt = 0;
        while (*p && cnt < N) {
            while (*p == ' ' || *p == '\t') p++;
            if (*p == '\n' || *p == '\0') break;
            int v = (int)strtol(p, &p, 10);
            parent[++cnt] = v;
        }
        if (cnt == 0) continue;
        if (cnt != N) die("wrong token count on line");

        /* init DP: A_v = x, B_v = 1 */
        for (int v = 1; v <= N; v++) {
            A[v][0] = 0; A[v][1] = 1; lenA[v] = 2;
            B[v][0] = 1; lenB[v] = 1;
        }
        /* merge children upward: parent[v] < v guaranteed */
        for (int v = N; v >= 2; v--) {
            int u = parent[v];
            /* AB = A_v + B_v */
            static u64 AB[MAXN + 2];
            int lab = lenA[v] > lenB[v] ? lenA[v] : lenB[v];
            for (int i = 0; i < lab; i++) {
                u64 a = i < lenA[v] ? A[v][i] : 0;
                u64 b = i < lenB[v] ? B[v][i] : 0;
                u64 s = a + b;
                if (s < a) die("overflow in add");
                AB[i] = s;
            }
            polymul(A[u], &lenA[u], B[v], lenB[v]);
            polymul(B[u], &lenB[u], AB, lab);
        }
        int nc = lenA[1] > lenB[1] ? lenA[1] : lenB[1];
        for (int i = 0; i < nc; i++) {
            u64 a = i < lenA[1] ? A[1][i] : 0;
            u64 b = i < lenB[1] ? B[1][i] : 0;
            u64 s = a + b;
            if (s < a) die("overflow in final add");
            coef[i] = s;
        }
        while (nc > 1 && coef[nc - 1] == 0) nc--;
        trees_checked++;
        if (dump_coefs) {
            for (int i = 0; i < nc; i++) printf("%llu%s", coef[i], i==nc-1?"\n":",");
        }

        /* unimodality check: strict decrease followed by strict increase */
        int falling = 0, viol = 0;
        for (int i = 1; i < nc; i++) {
            if (coef[i] > coef[i - 1]) { if (falling) { viol = 1; break; } }
            else if (coef[i] < coef[i - 1]) falling = 1;
        }

        /* margin: min over b in 1..nc-2 of coef[b] - min(prefmax_{<b}, sufmax_{>b}) */
        {
            static u64 prefmax[MAXN + 2], sufmax[MAXN + 2];
            prefmax[0] = coef[0];
            for (int i = 1; i < nc; i++) prefmax[i] = coef[i] > prefmax[i-1] ? coef[i] : prefmax[i-1];
            sufmax[nc - 1] = coef[nc - 1];
            for (int i = nc - 2; i >= 0; i--) sufmax[i] = coef[i] > sufmax[i+1] ? coef[i] : sufmax[i+1];
            for (int b = 1; b < nc - 1; b++) {
                u64 side = prefmax[b-1] < sufmax[b+1] ? prefmax[b-1] : sufmax[b+1];
                long long m = (long long)coef[b] - (long long)side;
                /* coef fits in <2^62 so cast ok */
                if (m < min_margin) {
                    min_margin = m;
                    report_tree(min_margin_tree, sizeof min_margin_tree);
                }
            }
        }

        /* log-concavity: coef[b]^2 >= coef[b-1]*coef[b+1] */
        int nlc = 0;
        for (int b = 1; b < nc - 1; b++) {
            u128 lhs = (u128)coef[b] * coef[b];
            u128 rhs = (u128)coef[b-1] * coef[b+1];
            if (lhs < rhs) { nlc = 1; break; }
        }
        if (nlc) {
            nonlogconcave_count++;
            if (nonlogconcave_count <= 20) {
                char buf[512]; report_tree(buf, sizeof buf);
                printf("NONLOGCONCAVE\t%s\t", buf);
                for (int i = 0; i < nc; i++) printf("%llu%s", coef[i], i==nc-1?"\n":",");
            }
            if (!first_nlc_tree[0]) report_tree(first_nlc_tree, sizeof first_nlc_tree);
        }

        if (viol) {
            violations++;
            char buf[512]; report_tree(buf, sizeof buf);
            printf("VIOLATION\t%s\t", buf);
            for (int i = 0; i < nc; i++) printf("%llu%s", coef[i], i==nc-1?"\n":",");
            fflush(stdout);
        }
    }

    printf("SUMMARY n=%d trees=%llu violations=%llu nonlogconcave=%llu min_margin=%lld min_margin_tree=%s\n",
           N, trees_checked, violations, nonlogconcave_count, min_margin,
           min_margin_tree[0] ? min_margin_tree : "-");
    return violations ? 1 : 0;
}
