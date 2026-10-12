// Check of the construction of 3-good partitions of [n] = {1, ..., n} in C++17.
//
// The construction of Theorem 1.2 of the paper is written here as a class whose
// methods return the parts as vectors.  For every n <= NMAX and for a list of
// larger n the program checks that each part has at most three distinct
// elements, that its sum is a power of 3, and that the parts cover [n] exactly
// once; it also checks Lemma 2.1, Lemma 3.2 and the invariant H(n) of
// Proposition 4.1.
//
// Usage: ./check [NMAX]   (default 10000)
#include <algorithm>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <set>
#include <stdexcept>
#include <string>
#include <vector>

using i64 = std::int64_t;
using Part = std::vector<i64>;
using Parts = std::vector<Part>;

static i64 pow3(int t) { i64 p = 1; for (int i = 0; i < t; ++i) p *= 3; return p; }
static int level(i64 n) { int t = 0; while (pow3(t + 1) <= n) ++t; return t; }
static bool isPow3(i64 s) { if (s < 1) return false; while (s % 3 == 0) s /= 3; return s == 1; }
static void require(bool c, const std::string &msg) { if (!c) throw std::runtime_error(msg); }

// Lemma 2.1: [-l, l], l mod 3 != 2, as {0} and zero-sum triples, mapped by x -> c + s x.
static void zsInterval(i64 l, i64 c, i64 s, Parts &out) {
    require(l >= 0 && l % 3 != 2, "zsInterval: bad l");
    i64 k;
    if (l % 3 == 0) { k = l / 3; out.push_back({c}); }
    else { k = (l - 1) / 3; out.push_back({c - s * l, c, c + s * l}); }
    for (i64 i = 0; i < k; ++i) {
        out.push_back({c - s * (3 * k - i), c + s * (1 + i), c + s * (3 * k - 1 - 2 * i)});
        out.push_back({c - s * (2 * k - i), c - s * (k - i), c + s * (3 * k - 2 * i)});
    }
}

// Lemma 3.2: the involution sigma_N of [1, 2N - 2].
static i64 sigma(i64 N, i64 x) {
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

static std::vector<std::pair<i64, i64>> pairsOf(i64 N) {
    std::vector<std::pair<i64, i64>> ps;
    if (N == 1) return ps;
    for (i64 z = 1; z <= 2 * N - 2; ++z) if (z < sigma(N, z)) ps.emplace_back(z, sigma(N, z));
    return ps;
}

// The partition of Delta_N into {0} and zero-sum triples, mapped by x -> P + x.
static void deltaParts(i64 N, i64 P, Parts &out) {
    if (N == 1) { out.push_back({P}); return; }
    if (N % 2 == 0) {
        i64 M = N / 2;
        out.push_back({P + 4 * M - 2, P - 2 * M, P - (2 * M - 2)});
        zsInterval(M - 2, P, 2, out);
    } else {
        i64 M = (N - 1) / 2;
        out.push_back({P + 4 * M, P - (2 * M + 1), P - (2 * M - 1)});
        out.push_back({P + 4 * M - 4, P - 2 * M, P - (2 * M - 4)});
        zsInterval(M - 3, P, 2, out);
    }
}

static void part(i64 n, Parts &out);

// Proposition 4.1: [1, n] minus {n - 1, n, 3^(t+1) - 2n + 1}.
static void hyp(i64 n, int t, Parts &out) {
    const i64 T = pow3(t), j = n - T;
    require(j % 3 == 2 && j >= 2 && 2 * j + 1 <= T, "hyp: out of range");
    std::vector<char> inD(static_cast<std::size_t>(T + 1), 0);
    if (j == 2) {
        inD[3] = 1;
        out.push_back({3});
        out.push_back({T});
    } else {
        const int u = level(j);
        const i64 P = pow3(u + 1);
        if (3 * j > T || 2 * j + 1 <= P) {
            for (i64 x = 1; x <= j - 2; ++x) inD[x] = 1;
            inD[2 * j - 1] = 1;
            zsInterval(j - 2, T, 1, out);
            if (3 * j > T) hyp(j, t - 1, out);
            else { hyp(j, u, out); out.push_back({P - 2 * j + 1, 2 * j - 1}); }
        } else {
            const i64 N = j - (P - 1) / 2, e = P - 1 - j;
            for (i64 x = 1; x <= e; ++x) inD[x] = 1;
            inD[P + 2 * N - 2] = 1;
            zsInterval(e, T, 1, out);
            for (auto [z, w] : pairsOf(N)) {
                inD[P + z + w - (2 * N + 1)] = 1;
                out.push_back({T + e + z, T + e + w, T - (2 * e + z + w)});
            }
            part(e, out);
            deltaParts(N, P, out);
        }
    }
    for (i64 x = 1; 2 * x < T; ++x) if (!inD[x] && !inD[T - x]) out.push_back({x, T - x});
}

static void part(i64 n, Parts &out) {
    if (n == 0) return;
    if (n == 1) { out.push_back({1}); return; }
    if (n == 2) { out.push_back({1, 2}); return; }
    const int t = level(n);
    const i64 T = pow3(t);
    if (n == T) { part(T - 1, out); out.push_back({T}); return; }
    if (2 * n >= 3 * T + 1) {
        const i64 a = 3 * T - 1 - n;
        part(a, out);
        for (i64 x = a + 1; 2 * x < 3 * T; ++x) out.push_back({x, 3 * T - x});
        return;
    }
    const i64 j = n - T;
    if (j % 3 != 2) { part(T - j - 1, out); zsInterval(j, T, 1, out); return; }
    hyp(n, t, out);
    out.push_back({n - 1, n, 3 * T - 2 * n + 1});
}

// Parts admissible and covering [1, n] minus `skip` exactly once.
static void verify(const Parts &ps, i64 n, const std::set<i64> &skip, const std::string &label) {
    std::vector<char> seen(static_cast<std::size_t>(n + 1), 0);
    for (i64 s : skip) seen[s] = 1;
    i64 covered = 0;
    for (const Part &p : ps) {
        require(!p.empty() && p.size() <= 3, label + ": part size");
        i64 sum = 0;
        for (i64 x : p) {
            require(x >= 1 && x <= n && !seen[x], label + ": element out of range or repeated");
            seen[x] = 1;
            sum += x;
            ++covered;
        }
        require(isPow3(sum), label + ": part sum is not a power of 3");
    }
    require(covered + static_cast<i64>(skip.size()) == n, label + ": not a cover");
}

static void checkInterval(i64 lmax) {
    for (i64 l = 0; l <= lmax; ++l) {
        if (l % 3 == 2) continue;
        Parts ps;
        zsInterval(l, 0, 1, ps);
        std::vector<i64> flat;
        for (const Part &p : ps) {
            require(p.size() == 1 ? p[0] == 0 : (p.size() == 3 && p[0] + p[1] + p[2] == 0), "Lemma 2.1 part");
            flat.insert(flat.end(), p.begin(), p.end());
        }
        std::sort(flat.begin(), flat.end());
        for (std::size_t i = 0; i < flat.size(); ++i) require(flat[i] == -l + static_cast<i64>(i), "Lemma 2.1 cover");
        require(static_cast<i64>(flat.size()) == 2 * l + 1, "Lemma 2.1 size");
    }
}

static void checkSigma(i64 nmax) {
    for (i64 N = 1; N <= nmax; N += 3) {
        const i64 K = 2 * N - 2;
        if (N > 1)
            for (i64 x = 1; x <= K; ++x) {
                const i64 y = sigma(N, x);
                require(y >= 1 && y <= K && y != x && sigma(N, y) == x, "Lemma 3.2 involution");
            }
        std::multiset<i64> delta{2 * N - 2};
        std::set<i64> sums;
        for (auto [z, w] : pairsOf(N)) {
            require(sums.insert(z + w).second, "Lemma 3.2 sums distinct");
            const i64 d = z + w - (2 * N + 1);
            require(d <= 0 || d % 2 == 0, "Lemma 3.2 positive values even");
            delta.insert(d);
        }
        Parts ps;
        deltaParts(N, 0, ps);
        std::multiset<i64> flat;
        for (const Part &p : ps) {
            require(p.size() == 1 ? p[0] == 0 : (p.size() == 3 && p[0] + p[1] + p[2] == 0), "Lemma 3.2 part");
            flat.insert(p.begin(), p.end());
        }
        require(flat == delta, "Lemma 3.2 cover");
        require(std::set<i64>(delta.begin(), delta.end()).size() == delta.size(), "Lemma 3.2 values distinct");
    }
}

int main(int argc, char **argv) {
    try {
        const i64 nmax = argc > 1 ? std::atoll(argv[1]) : 10000;
        checkInterval(30000);
        std::cout << "Lemma 2.1: [-l, l] for l <= 30000, l mod 3 != 2: ok\n";
        checkSigma(30001);
        std::cout << "Lemma 3.2: sigma_N for N <= 30001, N = 1 mod 3: ok\n";
        i64 countH = 0;
        for (i64 n = 1; n <= nmax; ++n) {
            Parts ps;
            part(n, ps);
            verify(ps, n, {}, "n = " + std::to_string(n));
            const int t = level(n);
            const i64 T = pow3(t), j = n - T;
            if (t >= 1 && j % 3 == 2 && j >= 2 && 2 * j + 1 <= T) {
                Parts hs;
                hyp(n, t, hs);
                verify(hs, n, {n - 1, n, 3 * T - 2 * n + 1}, "H(" + std::to_string(n) + ")");
                ++countH;
            }
        }
        std::cout << "Theorem 1.2: 3-good partitions of [n] for all n <= " << nmax << ": ok\n";
        std::cout << "Proposition 4.1: invariant H(n) for the " << countH << " values n <= " << nmax
                  << " where it applies: ok\n";
        const std::vector<i64> big = {pow3(13) + 2, pow3(13) + pow3(11) + 5, pow3(14) + (pow3(12) - 1) / 2 + 2,
                                      pow3(15) + pow3(12) + pow3(9) + pow3(6) + 2, 12345678};
        for (i64 n : big) { Parts ps; part(n, ps); verify(ps, n, {}, "n = " + std::to_string(n)); }
        std::cout << "Theorem 1.2: " << big.size() << " larger values of n up to "
                  << *std::max_element(big.begin(), big.end()) << ": ok\n";
        std::cout << "C++ check passed.\n";
    } catch (const std::exception &e) {
        std::cerr << "FAIL: " << e.what() << "\n";
        return 1;
    }
    return 0;
}
