"""Check of the construction of 3-good partitions of [n] = {1, ..., n}.

The program builds, for every n up to a bound and for a list of larger n,
the partition of [n] given in the paper (Theorem 1.2) and checks that every
part has at most three elements and a sum that is a power of 3, and that the
parts cover [n] exactly once.  It also checks the intermediate statements:
Lemma 2.1 (zero-sum triples on [-l, l]), Lemma 3.2 (the involutions sigma_N) and
the invariant H(n) of Proposition 4.1.

Usage: python3 check.py [NMAX]   (default 3000)
"""
import sys

sys.setrecursionlimit(10000)


def level(n):
    """The t with 3^t <= n < 3^(t+1), for n >= 1."""
    t = 0
    while 3 ** (t + 1) <= n:
        t += 1
    return t


def is_power_of_3(s):
    if s < 1:
        return False
    while s % 3 == 0:
        s //= 3
    return s == 1


def zs_interval(l):
    """Lemma 2.1: [-l, l], l mod 3 != 2, as {0} and zero-sum triples."""
    assert l >= 0 and l % 3 != 2
    if l % 3 == 0:
        k = l // 3
        parts = [(0,)]
    else:
        k = (l - 1) // 3
        parts = [(-l, 0, l)]
    for i in range(k):
        parts.append((-(3 * k - i), 1 + i, 3 * k - 1 - 2 * i))
        parts.append((-(2 * k - i), -(k - i), 3 * k - 2 * i))
    return parts


def shift(parts, c, s=1):
    return [tuple(c + s * x for x in p) for p in parts]


def sigma(N, x):
    """The involution sigma_N of [1, 2N - 2] (Lemma 3.2), N = 1 mod 3, N >= 4."""
    if N % 2 == 0:
        table = {1: N, N: 1, 2: N + 1, N + 1: 2}
        if x in table:
            return table[x]
        return x + N - 1 if x <= N - 1 else x - (N - 1)
    table = {1: N, N: 1, 2: N + 1, N + 1: 2, 2 * N - 3: 2 * N - 2, 2 * N - 2: 2 * N - 3,
             3: N - 1, N - 1: 3, 4: N + 2, N + 2: 4}
    if x in table:
        return table[x]
    return x + N - 2 if x <= N - 2 else x - (N - 2)


def pairs_of(N):
    """The pairs {z, sigma(z)}, z < sigma(z), of [1, 2N - 2]."""
    if N == 1:
        return []
    return [(z, sigma(N, z)) for z in range(1, 2 * N - 1) if z < sigma(N, z)]


def delta_parts(N):
    """The partition of Delta_N into {0} and zero-sum triples (Lemma 3.2)."""
    if N == 1:
        return [(0,)]
    if N % 2 == 0:
        M = N // 2
        return [(4 * M - 2, -2 * M, -(2 * M - 2))] + shift(zs_interval(M - 2), 0, 2)
    M = (N - 1) // 2
    return ([(4 * M, -(2 * M + 1), -(2 * M - 1)), (4 * M - 4, -2 * M, -(2 * M - 4))]
            + shift(zs_interval(M - 3), 0, 2))


def part(n):
    """A 3-good partition of [1, n] (Theorem 1.2)."""
    if n == 0:
        return []
    if n == 1:
        return [(1,)]
    if n == 2:
        return [(1, 2)]
    t = level(n)
    T = 3 ** t
    if n == T:
        return part(T - 1) + [(T,)]
    if 2 * n >= 3 * T + 1:
        a = 3 * T - 1 - n
        return part(a) + [(x, 3 * T - x) for x in range(a + 1, (3 * T - 1) // 2 + 1)]
    j = n - T
    if j % 3 != 2:
        return part(T - j - 1) + shift(zs_interval(j), T)
    return hyp(n, t) + [(n - 1, n, 3 * T - 2 * n + 1)]


def hyp(n, t):
    """A 3-good partition of [1, n] minus {n - 1, n, 3^(t+1) - 2n + 1}, for
    n = 3^t + j with j = 2 mod 3 and 2 <= j <= (3^t - 1)/2 (Proposition 4.1)."""
    T = 3 ** t
    j = n - T
    assert j % 3 == 2 and 2 <= j and 2 * j + 1 <= T
    if j == 2:
        D = {3}
        F = [(3,)]
        R = [(T,)]
    elif 3 * j > T or 2 * j + 1 <= 3 ** (level(j) + 1):
        D = set(range(1, j - 1)) | {2 * j - 1}
        R = shift(zs_interval(j - 2), T)
        if 3 * j > T:                       # case B
            F = hyp(j, t - 1)
        else:                               # case A1
            u = level(j)
            F = hyp(j, u) + [(3 ** (u + 1) - 2 * j + 1, 2 * j - 1)]
    else:                                   # case A2
        P = 3 ** (level(j) + 1)
        N = j - (P - 1) // 2
        e = P - 1 - j
        prs = pairs_of(N)
        Delta = [2 * N - 2] + [z + w - (2 * N + 1) for z, w in prs]
        D = set(range(1, e + 1)) | {P + d for d in Delta}
        R = shift(zs_interval(e), T) + [(T + e + z, T + e + w, T - (2 * e + z + w)) for z, w in prs]
        F = part(e) + shift(delta_parts(N), P)
    E = [(x, T - x) for x in range(1, (T - 1) // 2 + 1) if x not in D and T - x not in D]
    return E + F + R


def check_cover(parts, target, label):
    """Parts of size <= 3, power-of-3 sums, covering `target` exactly once."""
    seen = []
    for p in parts:
        if len(p) > 3 or len(set(p)) != len(p) or not is_power_of_3(sum(p)):
            raise AssertionError(f"{label}: bad part {p}")
        seen.extend(p)
    if sorted(seen) != sorted(target):
        raise AssertionError(f"{label}: parts do not cover the target set exactly once")


def check_interval(LMAX):
    for l in range(LMAX + 1):
        if l % 3 == 2:
            continue
        parts = zs_interval(l)
        flat = sorted(x for p in parts for x in p)
        assert flat == list(range(-l, l + 1)), l
        for p in parts:
            assert p == (0,) or (len(p) == 3 and len(set(p)) == 3 and sum(p) == 0), (l, p)


def check_sigma(NMAX):
    for N in range(1, NMAX + 1, 3):
        K = 2 * N - 2
        if N > 1:
            for x in range(1, K + 1):
                y = sigma(N, x)
                assert 1 <= y <= K and y != x and sigma(N, y) == x, (N, x)
        prs = pairs_of(N)
        sums = [z + w for z, w in prs]
        assert len(set(sums)) == len(sums), N
        Delta = [2 * N - 2] + [s - (2 * N + 1) for s in sums]
        assert len(set(Delta)) == len(Delta), N
        for d in Delta:
            assert d <= 0 or d % 2 == 0, (N, d)
            assert -(2 * N - 2) <= d <= 2 * N - 2, (N, d)
        parts = delta_parts(N)
        flat = sorted(x for p in parts for x in p)
        assert flat == sorted(Delta), N
        for p in parts:
            assert p == (0,) or (len(p) == 3 and len(set(p)) == 3 and sum(p) == 0), (N, p)


def main():
    NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 3000
    check_interval(3000)
    print("Lemma 2.1: [-l, l] for l <= 3000, l mod 3 != 2: ok")
    check_sigma(3001)
    print("Lemma 3.2: sigma_N for N <= 3001, N = 1 mod 3: ok")
    count_h = 0
    for n in range(1, NMAX + 1):
        check_cover(part(n), range(1, n + 1), f"n={n}")
        t = level(n)
        T = 3 ** t
        j = n - T
        if t >= 1 and j % 3 == 2 and j >= 2 and 2 * j + 1 <= T:
            tri = {n - 1, n, 3 * T - 2 * n + 1}
            check_cover(hyp(n, t), [x for x in range(1, n + 1) if x not in tri], f"H({n})")
            count_h += 1
    print(f"Theorem 1.2: 3-good partitions of [n] for all n <= {NMAX}: ok")
    print(f"Proposition 4.1: invariant H(n) for the {count_h} values n <= {NMAX} where it applies: ok")
    big = [3 ** 9 + 2, 3 ** 9 + 3 ** 8 - 1, 3 ** 10 + 3 ** 7 + 2, 3 ** 11 + 3 ** 10 // 2 - 1,
           3 ** 11 + (3 ** 9 - 1) // 2 + 2, 3 ** 12 + 3 ** 11 + 5, 3 ** 12 + 33335,
           3 ** 13 + 3 ** 8 + 3 ** 3 + 2, 2 * 10 ** 6 + 1, 3 ** 13 + 3 ** 11 + 3 ** 9 + 3 ** 7 + 2]
    for n in big:
        check_cover(part(n), range(1, n + 1), f"n={n}")
    print(f"Theorem 1.2: {len(big)} larger values of n up to {max(big)}: ok")
    print("Python check passed.")


if __name__ == "__main__":
    main()
