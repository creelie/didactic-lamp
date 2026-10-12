/* Check of the construction of 3-good partitions of [n] = {1, ..., n} in C.
 *
 * For every n <= NMAX and for a list of larger n, the program builds the
 * partition of [n] of Theorem 1.2 of the paper and checks that each part has at
 * most three distinct elements, that its sum is a power of 3, and that the
 * parts cover [n] exactly once.  For the n where it applies it also checks
 * the invariant H(n) of Proposition 4.1.
 *
 * Usage: ./check [NMAX]   (default 30000)
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef long long ll;
typedef struct { ll a, b, c; int k; } Part;   /* k = number of elements (1..3) */

static Part *parts;
static size_t nparts, capparts;

static void die(const char *msg, ll n) {
    fprintf(stderr, "FAIL: %s (n = %lld)\n", msg, n);
    exit(1);
}

static void add(int k, ll a, ll b, ll c) {
    if (nparts == capparts) {
        capparts = capparts ? 2 * capparts : 1024;
        parts = realloc(parts, capparts * sizeof(Part));
        if (!parts) die("out of memory", 0);
    }
    parts[nparts].a = a; parts[nparts].b = b; parts[nparts].c = c; parts[nparts].k = k;
    nparts++;
}

static ll pow3(int t) { ll p = 1; while (t-- > 0) p *= 3; return p; }

static int level(ll n) { int t = 0; while (pow3(t + 1) <= n) t++; return t; }

/* Lemma 2.1: [-l, l] (l mod 3 != 2) as {0} and zero-sum triples, each part
   mapped by x -> c + s x. */
static void zs_interval(ll l, ll c, ll s) {
    ll k;
    if (l < 0 || l % 3 == 2) die("zs_interval: bad l", l);
    if (l % 3 == 0) { k = l / 3; add(1, c, 0, 0); }
    else { k = (l - 1) / 3; add(3, c - s * l, c, c + s * l); }
    for (ll i = 0; i < k; i++) {
        add(3, c - s * (3 * k - i), c + s * (1 + i), c + s * (3 * k - 1 - 2 * i));
        add(3, c - s * (2 * k - i), c - s * (k - i), c + s * (3 * k - 2 * i));
    }
}

/* Lemma 3.2: the involution sigma_N of [1, 2N - 2], N = 1 mod 3, N >= 4. */
static ll sigma(ll N, ll x) {
    if (x == 1) return N;
    if (x == N) return 1;
    if (x == 2) return N + 1;
    if (x == N + 1) return 2;
    if (N % 2 == 0) return x <= N - 1 ? x + N - 1 : x - (N - 1);
    if (x == 2 * N - 3) return 2 * N - 2;
    if (x == 2 * N - 2) return 2 * N - 3;
    if (x == 3) return N - 1;
    if (x == N - 1) return 3;
    if (x == 4) return N + 2;
    if (x == N + 2) return 4;
    return x <= N - 2 ? x + N - 2 : x - (N - 2);
}

/* The partition of Delta_N into {0} and zero-sum triples, shifted by P. */
static void delta_parts(ll N, ll P) {
    if (N == 1) { add(1, P, 0, 0); return; }
    if (N % 2 == 0) {
        ll M = N / 2;
        add(3, P + 4 * M - 2, P - 2 * M, P - (2 * M - 2));
        zs_interval(M - 2, P, 2);
    } else {
        ll M = (N - 1) / 2;
        add(3, P + 4 * M, P - (2 * M + 1), P - (2 * M - 1));
        add(3, P + 4 * M - 4, P - 2 * M, P - (2 * M - 4));
        zs_interval(M - 3, P, 2);
    }
}

static void part(ll n);

/* Proposition 4.1: [1, n] minus {n - 1, n, 3^(t+1) - 2n + 1}. */
static void hyp(ll n, int t) {
    ll T = pow3(t), j = n - T;
    unsigned char *D;
    if (j % 3 != 2 || j < 2 || 2 * j + 1 > T) die("hyp: out of range", n);
    D = calloc((size_t)T + 1, 1);
    if (!D) die("out of memory", n);
    if (j == 2) {
        D[3] = 1;
        add(1, 3, 0, 0);
        add(1, T, 0, 0);
    } else {
        int u = level(j);
        ll U3 = pow3(u + 1);
        if (3 * j > T || 2 * j + 1 <= U3) {
            for (ll x = 1; x <= j - 2; x++) D[x] = 1;
            D[2 * j - 1] = 1;
            zs_interval(j - 2, T, 1);
            if (3 * j > T) hyp(j, t - 1);                       /* case B */
            else { hyp(j, u); add(2, U3 - 2 * j + 1, 2 * j - 1, 0); }  /* case A1 */
        } else {                                                /* case A2 */
            ll P = U3, N = j - (P - 1) / 2, e = P - 1 - j;
            for (ll x = 1; x <= e; x++) D[x] = 1;
            D[P + 2 * N - 2] = 1;
            zs_interval(e, T, 1);
            if (N > 1)
                for (ll z = 1; z <= 2 * N - 2; z++) {
                    ll w = sigma(N, z);
                    if (z < w) {
                        D[P + z + w - (2 * N + 1)] = 1;
                        add(3, T + e + z, T + e + w, T - (2 * e + z + w));
                    }
                }
            part(e);
            delta_parts(N, P);
        }
    }
    for (ll x = 1; 2 * x < T; x++)
        if (!D[x] && !D[T - x]) add(2, x, T - x, 0);
    free(D);
}

static void part(ll n) {
    int t;
    ll T, j;
    if (n == 0) return;
    if (n == 1) { add(1, 1, 0, 0); return; }
    if (n == 2) { add(2, 1, 2, 0); return; }
    t = level(n); T = pow3(t);
    if (n == T) { part(T - 1); add(1, T, 0, 0); return; }
    if (2 * n >= 3 * T + 1) {
        ll a = 3 * T - 1 - n;
        part(a);
        for (ll x = a + 1; 2 * x < 3 * T; x++) add(2, x, 3 * T - x, 0);
        return;
    }
    j = n - T;
    if (j % 3 != 2) { part(T - j - 1); zs_interval(j, T, 1); return; }
    hyp(n, t);
    add(3, n - 1, n, 3 * T - 2 * n + 1);
}

static int is_pow3(ll s) {
    if (s < 1) return 0;
    while (s % 3 == 0) s /= 3;
    return s == 1;
}

/* Every part admissible; the parts cover [1, n] minus `skip` exactly once. */
static void verify(ll n, const ll *skip, int nskip, const char *label) {
    unsigned char *cnt = calloc((size_t)n + 1, 1);
    size_t covered = 0;
    if (!cnt) die("out of memory", n);
    for (int i = 0; i < nskip; i++) cnt[skip[i]] = 1;
    for (size_t i = 0; i < nparts; i++) {
        Part p = parts[i];
        ll v[3] = {p.a, p.b, p.c}, s = 0;
        for (int q = 0; q < p.k; q++) {
            if (v[q] < 1 || v[q] > n) die(label, n);
            if (cnt[v[q]]) die(label, n);
            cnt[v[q]] = 1;
            s += v[q];
            covered++;
        }
        if (!is_pow3(s)) die(label, n);
    }
    if (covered + (size_t)nskip != (size_t)n) die(label, n);
    free(cnt);
}

int main(int argc, char **argv) {
    ll nmax = argc > 1 ? atoll(argv[1]) : 30000;
    ll count_h = 0;
    for (ll n = 1; n <= nmax; n++) {
        int t = level(n);
        ll T = pow3(t), j = n - T;
        nparts = 0; part(n); verify(n, NULL, 0, "partition of [n]");
        if (t >= 1 && j % 3 == 2 && j >= 2 && 2 * j + 1 <= T) {
            ll skip[3] = {n - 1, n, 3 * T - 2 * n + 1};
            nparts = 0; hyp(n, t); verify(n, skip, 3, "invariant H(n)");
            count_h++;
        }
    }
    printf("Theorem 1.2: 3-good partitions of [n] for all n <= %lld: ok\n", nmax);
    printf("Proposition 4.1: invariant H(n) for the %lld values n <= %lld where it applies: ok\n",
           count_h, nmax);
    {
        ll big[] = {pow3(14) + 2, pow3(14) + pow3(12) + pow3(10) + 2, pow3(15) + (pow3(13) - 1) / 2 + 2,
                    pow3(15) + pow3(14) / 2, 10000001, pow3(16) + pow3(13) + pow3(11) + pow3(9) + 2,
                    pow3(16) + (pow3(16) - 1) / 2};
        int nb = (int)(sizeof big / sizeof big[0]);
        for (int i = 0; i < nb; i++) { nparts = 0; part(big[i]); verify(big[i], NULL, 0, "large n"); }
        printf("Theorem 1.2: %d larger values of n up to %lld: ok\n", nb, big[nb - 1]);
    }
    printf("C check passed.\n");
    free(parts);
    return 0;
}
