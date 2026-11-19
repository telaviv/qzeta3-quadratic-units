# Exact check (Fractions, truncated power series) of the frozen Lean definitions in QZeta3/Defs.lean.
#   cc n s j q = coeff_{4-s} of G_j(u) = N(q^-j (1-u)) * (prod_{j'!=j} (1 - q^{j'} q^-j (1-u))^4)^-1
#   P3 = sum_j (c_{3,j} + 2 c_{4,j});  P0 = -sum c_{s,j} W_{s,j}
# Checks: PF identity at sample T, sum c = 0, Recip (P3(1/q) = q^-n P3, P0(1/q) = -q^-n P0),
# integrality denominators at q = 1/p, size of S_n, and the expansion S_n = P0 + P3 zeta_q(3) (mpmath).
from fractions import Fraction as Fr
import mpmath as mp
import sys

M = 4  # truncation order in u

def smul(a, b):
    r = [0] * M
    for i in range(M):
        if a[i] == 0: continue
        for k in range(M - i):
            r[i + k] += a[i] * b[k]
    return r

def sinv(a):
    r = [0] * M
    r[0] = 1 / a[0]
    for k in range(1, M):
        r[k] = -sum(a[i] * r[k - i] for i in range(1, k + 1)) / a[0]
    return r

def lin(a, b):  # a + b u
    return [a, b] + [0] * (M - 2)

def factor(y, q, j):  # 1 - y T, T = q^-j (1-u)
    t = y * q**(-j)
    return lin(1 - t, t)

def qpoch(x, q, m):
    r = 1
    for i in range(m): r *= (1 - x * q**i)
    return r

def cc(n, q):
    c = {}
    for j in range(n + 1):
        G = [qpoch(q, q, n)**2] + [0] * (M - 1)
        for i in range(n):
            G = smul(G, factor(q**(-n) * q**i, q, j))
            G = smul(G, factor(q**(n + 1) * q**i, q, j))
        Tser = lin(q**(-j), -q**(-j))
        for _ in range(n): G = smul(G, Tser)
        D = [1] + [0] * (M - 1)
        for jp in range(n + 1):
            if jp != j:
                f = factor(q**jp, q, j)
                for _ in range(4): D = smul(D, f)
        G = smul(G, sinv(D))
        for s in range(1, 5): c[(s, j)] = G[4 - s]
    return c

def Rfun(n, q, T):
    return qpoch(q, q, n)**2 * qpoch(q**(-n) * T, q, n) * qpoch(q**(n + 1) * T, q, n) * T**n / qpoch(T, q, n + 1)**4

def P3(n, q, c): return sum(c[(3, j)] + 2 * c[(4, j)] for j in range(n + 1))
def W(n, q, s, j):
    return sum((1 - q**m)**(-s) - 1 for m in range(1, j + 1)) - sum((1 - q**(-m))**(-s) for m in range(1, n - j + 1))
def P0(n, q, c): return -sum(c[(s, j)] * W(n, q, s, j) for s in range(1, 5) for j in range(n + 1))

for n in range(1, 7):
    q = Fr(2, 7)
    c = cc(n, q)
    for Tv in [Fr(3, 11), Fr(-5, 3), Fr(0)]:
        rhs = sum(c[(s, j)] / (1 - q**j * Tv)**s for s in range(1, 5) for j in range(n + 1))
        assert Rfun(n, q, Tv) == rhs, ("PF", n, Tv)
    assert sum(c.values()) == 0
    qi = 1 / q
    ci = cc(n, qi)
    for k, v in c.items():
        s, j = k
        assert ci[(s, j)] == q**(-n) * c[(s, n - j)]
    assert P3(n, qi, ci) == q**(-n) * P3(n, q, c)
    assert P0(n, qi, ci) == -q**(-n) * P0(n, q, c)
    print("n", n, ": PF, sum c = 0, c-reciprocity, Recip OK", flush=True)

# integrality: at q = 1/p, d_n(q)^4 * P (times a power of p) should be p-integral only issue is p; check that
# the denominator of d_n(1/p)^4 P0, d_n(1/p)^4 P3 is a power of p.
def cyclo_vals(nmax, x):
    # Phi_l(x) via x^l - 1 = prod_{d|l} Phi_d(x)
    phi = {}
    for l in range(1, nmax + 1):
        v = x**l - 1
        for d in range(1, l):
            if l % d == 0: v /= phi[d]
        phi[l] = v
    return phi
def only_p(den, p):
    while den % p == 0: den //= p
    return den == 1
for p in [3, 5, 7]:
    for n in range(1, 6):
        q = Fr(1, p)
        c = cc(n, q)
        ph = cyclo_vals(n, q)
        dn = 1
        for l in range(1, n + 1): dn *= ph[l]
        for name, val in [("P0", P0(n, q, c)), ("P3", P3(n, q, c))]:
            assert only_p((dn**4 * val).denominator, p), (p, n, name)
        assert only_p((dn * P3(n, q, c)).denominator, p)
print("integrality (d_n^4 P0, d_n P3 at q = 1/p) OK", flush=True)

mp.mp.dps = 50
for sgn in [1, -1]:
    for n in [1, 2, 3, 4]:
        qm = sgn * ((3 - mp.sqrt(5)) / 2)
        # exact c over Q(sqrt5) is costly; use mpmath floats in the same truncated series code
        c = cc(n, qm)
        p3, p0 = P3(n, qm, c), P0(n, qm, c)
        S = mp.nsum(lambda k: Rfun(n, qm, qm**int(k)), [1, mp.inf]) - mp.nsum(lambda k: Rfun(n, qm, qm**(-n - int(k))), [1, mp.inf])
        z3 = mp.nsum(lambda m: m**2 * qm**m / (1 - qm**m), [1, mp.inf])
        print("sgn", sgn, "n", n, "S-(P0+P3 z3) =", mp.nstr(S - (p0 + p3 * z3), 5), " |S|/|q|^(n(n+1)) =", mp.nstr(abs(S) / abs(qm)**(n * (n + 1)), 6))
