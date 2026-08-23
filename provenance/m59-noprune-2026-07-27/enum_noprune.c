/* Exhaustive enumeration of USF (no-unique-sum) subsets of Z/pZ.
 *
 * USF: A subset of Z/pZ such that for every v in Z/pZ the number of unordered
 * pairs {i,j} (i<=j, loops allowed) of elements of A with a_i+a_j = v is never
 * exactly 1.
 *
 * Every affine class of a set with >=2 elements has a representative containing
 * 0 and 1, so we enumerate A = {0,1} u B with B a subset of {2,...,p-1}.
 * Output: affine-canonical representatives only (min bitmask over the n(n-1)
 * normalisations of the affine class), which is a complete transversal of affine
 * classes and hence of shapes.
 *
 * Exact integer / bitmask arithmetic only.
 *
 * usage: enum <p> <n> [--count-only] [--out FILE]
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

static int P, N;
static int cnt[64];
static uint64_t Smask, singles_mask, support_mask, FULL;
static int nsingles;
static int A[64];
static int alen;
static long long usf_count = 0, canon_count = 0, nodes = 0;
static int inv[64];
static FILE *out = NULL;
static int count_only = 0;

static inline void addv(int v) {
    int c = cnt[v]++;
    if (c == 0) { singles_mask |= 1ULL << v; support_mask |= 1ULL << v; nsingles++; }
    else if (c == 1) { singles_mask &= ~(1ULL << v); nsingles--; }
}
static inline void subv(int v) {
    int c = --cnt[v];
    if (c == 0) { singles_mask &= ~(1ULL << v); support_mask &= ~(1ULL << v); nsingles--; }
    else if (c == 1) { singles_mask |= 1ULL << v; nsingles++; }
}
static inline void addelem(int x) {
    for (int i = 0; i < alen; i++) { int v = x + A[i]; if (v >= P) v -= P; addv(v); }
    int v = (2 * x) % P; addv(v);
    A[alen++] = x; Smask |= 1ULL << x;
}
static inline void delelem(void) {
    int x = A[--alen]; Smask &= ~(1ULL << x);
    int v = (2 * x) % P; subv(v);
    for (int i = alen - 1; i >= 0; i--) { int w = x + A[i]; if (w >= P) w -= P; subv(w); }
}

/* affine canonicity: A (as bitmask Smask) must be the numerically smallest mask
 * among all images (a-u)*inv(v-u) over ordered pairs u!=v in A. */
static int affine_canonical(void) {
    for (int iu = 0; iu < alen; iu++) {
        int u = A[iu];
        for (int iv = 0; iv < alen; iv++) {
            if (iv == iu) continue;
            int d = A[iv] - u; if (d < 0) d += P;
            int di = inv[d];
            uint64_t m = 0;
            for (int k = 0; k < alen; k++) {
                int t = A[k] - u; if (t < 0) t += P;
                m |= 1ULL << ((t * di) % P);
            }
            if (m < Smask) return 0;
        }
    }
    return 1;
}

static void report(void) {
    usf_count++;
    if (!affine_canonical()) return;
    canon_count++;
    if (out) {
        for (int i = 0; i < alen; i++) fprintf(out, "%d%c", A[i], i + 1 == alen ? '\n' : ' ');
    }
}

static void rec(int start, int r) {
    nodes++;
    if (r == 1) {
        /* fast leaf: adding x hits H = rot(Smask,x) | bit(2x); all hits are distinct
         * because x is not in A. Need singles_mask subset of H and H disjoint from
         * the zero set (else a new singleton appears). */
        uint64_t zeros = FULL & ~support_mask;
        for (int x = start; x < P; x++) {
            uint64_t H = ((Smask << x) | (Smask >> (P - x))) & FULL;
            H |= 1ULL << ((2 * x) % P);
            if ((singles_mask & ~H) == 0 && (H & zeros) == 0) {
                addelem(x); report(); delelem();
            }
        }
        return;
    }
    /* counting prune: each of the remaining r elements adds pairs; the number of
     * new pairs is r*alen + r(r+1)/2, and each singleton needs at least one. */
    /* PRUNE DISABLED for verification */
    int last = P - r;
    for (int x = start; x <= last; x++) {
        addelem(x);
        rec(x + 1, r - 1);
        delelem();
    }
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: enum p n [--count-only] [--out FILE]\n"); return 1; }
    P = atoi(argv[1]); N = atoi(argv[2]);
    for (int i = 3; i < argc; i++) {
        if (!strcmp(argv[i], "--count-only")) count_only = 1;
        else if (!strcmp(argv[i], "--out") && i + 1 < argc) { out = fopen(argv[++i], "w"); }
    }
    if (P > 64) { fprintf(stderr, "p too large for 64-bit masks\n"); return 1; }
    if (N > P) { printf("%d %d 0 0 0\n", P, N); return 0; }
    FULL = (P == 64) ? ~0ULL : ((1ULL << P) - 1);
    for (int a = 1; a < P; a++) for (int b = 1; b < P; b++) if ((a * b) % P == 1) inv[a] = b;
    memset(cnt, 0, sizeof cnt);
    Smask = singles_mask = support_mask = 0; nsingles = 0; alen = 0;
    if (N == 1) { printf("%d %d 0 0 0\n", P, N); return 0; }
    addelem(0); addelem(1);
    if (N == 2) { /* {0,1}: sums 0,1,2 each once -> not USF */ printf("%d %d 0 0 0\n", P, N); return 0; }
    rec(2, N - 2);
    if (out) fclose(out);
    printf("%d %d %lld %lld %lld\n", P, N, usf_count, canon_count, nodes);
    return 0;
}
