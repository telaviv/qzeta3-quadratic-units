# Exact checks (Fractions) of the intermediate statements used in QZeta3/Denom.
# * Lagrange: a_{j'}(N) = N(x^-j') / den(j'), den(j') = prod_{j''!=j'} (1 - x^{j''} x^{-j'})
#   = U(j') qf(j') qf(n-j'), U(j') = prod_{i<j'} (-(x^{i+1})^-1).
# * a_1 = U^-1 G(n, j'), a_3 = U^-1 V G(j'+n, j') G(n, j'), a_4 = U^-1 G(n-j'+n, n-j') G(n, j'),
#   V = prod_{i<n} (-(x^{j'+1+i})^-1), G = Gaussian binomial by q-Pascal.
# * Gser = Tser^n E1^2 E3 E4, E = a_j + sum_{j'!=j} a_{j'} u/(alpha + beta u).
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from fractions import Fraction as Fr

M = 4
def smul(a, b):
    r = [0] * M
    for i in range(M):
        for k in range(M - i):
            r[i + k] += a[i] * b[k]
    return r
def sinv(a):
    r = [0] * M
    r[0] = 1 / a[0]
    for k in range(1, M):
        r[k] = -sum(a[i] * r[k - i] for i in range(1, k + 1)) / a[0]
    return r
def qpoch(y, q, m):
    r = 1
    for i in range(m): r *= (1 - y * q**i)
    return r
def qf(x, m): return qpoch(x, x, m)

from functools import lru_cache
def gauss(n, k, x):
    if k == 0: return Fr(1)
    if n == 0: return Fr(0)
    return gauss(n - 1, k - 1, x) + x**k * gauss(n - 1, k, x)

def Gser(n, q, j):
    G = [qf(q, n)**2] + [0] * (M - 1)
    def factor(y):
        t = y * q**(-j); return [1 - t, t] + [0] * (M - 2)
    for i in range(n):
        G = smul(G, factor(q**(-n) * q**i)); G = smul(G, factor(q**(n + 1) * q**i))
    for _ in range(n): G = smul(G, [q**(-j), -q**(-j)] + [0] * (M - 2))
    D = [1] + [0] * (M - 1)
    for jp in range(n + 1):
        if jp != j:
            for _ in range(4): D = smul(D, factor(q**jp))
    return smul(G, sinv(D))

for x in [Fr(2, 7), Fr(-3, 2), Fr(5, 3)]:
    for n in range(1, 6):
        # Gaussian identity
        for k in range(0, 6):
            for m in range(0, 6):
                assert qf(x, k) * qf(x, m) * gauss(k + m, k, x) == qf(x, k + m)
        N1 = lambda T: qf(x, n)
        N3 = lambda T: qpoch(x**(-n) * T, x, n)
        N4 = lambda T: qpoch(x**(n + 1) * T, x, n)
        a = {}
        for jp in range(n + 1):
            den = 1
            for jpp in range(n + 1):
                if jpp != jp: den *= (1 - x**jpp * x**(-jp))
            U = 1
            for i in range(jp): U *= -(x**(i + 1))**-1
            assert den == U * qf(x, jp) * qf(x, n - jp)
            V = 1
            for i in range(n): V *= -(x**(jp + 1 + i))**-1
            T = x**(-jp)
            a[(1, jp)] = N1(T) / den; a[(3, jp)] = N3(T) / den; a[(4, jp)] = N4(T) / den
            assert a[(1, jp)] == gauss(n, jp, x) / U
            assert a[(3, jp)] == V * gauss(jp + n, jp, x) * gauss(n, jp, x) / U
            assert a[(4, jp)] == gauss(n - jp + n, n - jp, x) * gauss(n, jp, x) / U
        # Lagrange identity at random T
        for Tv in [Fr(3, 11), Fr(-2, 9)]:
            for t, N in [(1, N1), (3, N3), (4, N4)]:
                rhs = 0
                for jp in range(n + 1):
                    pr = 1
                    for jpp in range(n + 1):
                        if jpp != jp: pr *= (1 - x**jpp * Tv)
                    rhs += a[(t, jp)] * pr
                assert rhs == N(Tv)
        for j in range(n + 1):
            def E(t):
                e = [a[(t, j)]] + [0] * (M - 1)
                for jp in range(n + 1):
                    if jp == j: continue
                    al = 1 - x**jp * x**(-j); be = x**jp * x**(-j)
                    g = [0] + [(-be)**(k - 1) * al**(-k) for k in range(1, M)]
                    e = [e[k] + a[(t, jp)] * g[k] for k in range(M)]
                return e
            P = [1] + [0] * (M - 1)
            for _ in range(n): P = smul(P, [x**(-j), -x**(-j)] + [0] * (M - 2))
            P = smul(P, E(1)); P = smul(P, E(1)); P = smul(P, E(3)); P = smul(P, E(4))
            assert P == Gser(n, x, j), (x, n, j)
    print("x =", x, "OK")
