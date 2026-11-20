"""Final referee: exact checks in Q(q) (sympy sparse rational-function field), general (A, r, n).

Checks per triple:
  wp    R(q^-n/T) = q^{An/2} T^A R(T)                       (Lemma 2.1)
  inv   R(T;1/q) = q^-e R(q^-n T;q)                          (Lemma 2.2)
  pf    R(T) = sum c_{s,j}(1-q^jT)^-s, sum c = 0             (2.1), c computed as [u^{A-s}] u^A R
  cinv  c_{s,j}(1/q) = q^-e c_{s,n-j}(q)                     (Cor 3.1)
  den   d_n^{A-s} c_{s,j} in Z[q^{+-1}]                       (Lemma 3.2)
  dgen  (A-1)! d_n^{A-l} P_l, d_n^A P_0 in Z[q^{+-1}]          (Lemma 8.1); info: is (A-1)! needed? d_n^{A-1}P_0?
  recip P_l(1/q) = q^-e P_l, P_0(1/q) = -q^-e P_0, Q_0 = 0     (Lemma 5.1)
  dsym  d_n(1/q) = -q^{-Tot(n)} d_n(q)                        (Section 8)
"""
import sys
from math import factorial
from fractions import Fraction
from sympy import QQ, ZZ, cyclotomic_poly, binomial, totient, symbols, Poly, Rational
from sympy.polys.fields import field

K, q, T = field("q,T", QQ)
one = K(1)


def qp(a, qq, m):
    p = one
    for i in range(m):
        p *= (1 - a * qq**i)
    return p


def R(A, r, n, TT, qq):
    e = (A - 2 * r) * n // 2
    return (qp(qq, qq, n)**(A - 2 * r) * qp(qq**(-r * n) * TT, qq, r * n) * qp(qq**(n + 1) * TT, qq, r * n)
            * TT**e / qp(TT, qq, n + 1)**A)


def smul(a, b, D):
    c = [0] * D
    for i in range(D):
        if a[i] == 0:
            continue
        for k in range(D - i):
            c[i + k] = c[i + k] + a[i] * b[k]
    return c


def coeffs(A, r, n, qq, unit):
    """c[(s,j)] via the Laurent expansion of u^A R at T = qq^-j (1-u), truncated at u^{A-1}."""
    e = (A - 2 * r) * n // 2
    D = A
    c = {}
    numexps = list(range(-r * n, 0)) + list(range(n + 1, n + r * n + 1))
    const = qp(qq, qq, n)**(A - 2 * r) if unit is one else None
    for j in range(n + 1):
        ser = [0] * D
        ser[0] = unit
        if const is not None:
            ser[0] = const
        else:
            pc = unit
            for i in range(n):
                pc = pc * (1 - qq**(i + 1))
            ser[0] = pc**(A - 2 * r)
        # T^e = qq^{-je} (1-u)^e
        te = [(int(binomial(e, k)) * (-1)**k) * unit for k in range(D)]
        te = [x * qq**(-j * e) for x in te]
        ser = smul(ser, te, D)
        for a in numexps:  # 1 - qq^a T = (1 - qq^{a-j}) + qq^{a-j} u
            f = [0] * D
            f[0] = 1 - qq**(a - j)
            if D > 1:
                f[1] = qq**(a - j)
            ser = smul(ser, f, D)
        for i in range(n + 1):
            if i == j:
                continue
            al = 1 - qq**(i - j)
            be = qq**(i - j)
            # (al + be u)^-A = al^-A sum_k binom(-A,k) (be/al)^k u^k
            g = [unit * int(binomial(-A, k)) * (be / al)**k / al**A for k in range(D)]
            ser = smul(ser, g, D)
        for s in range(1, A + 1):
            c[(s, j)] = ser[A - s]
    return c


def Cpoly_coeffs(s):
    x = symbols('x')
    p = Poly(binomial(x + s - 1, s - 1).expand(func=True), x)
    return {m[0]: QQ(int(cf.p), int(cf.q)) for m, cf in zip(p.monoms(), p.coeffs())}


def Wfun(n, qq, s, j, unit):
    w = 0 * unit
    for m in range(1, j + 1):
        w += 1 / (1 - qq**m)**s - 1
    for m in range(1, n - j + 1):
        w -= 1 / (1 - qq**(-m))**s
    return w


def forms(A, r, n, c, qq, unit):
    Cc = {s: Cpoly_coeffs(s) for s in range(1, A + 1)}
    P = {}
    for l in range(3, A, 2):
        P[l] = sum((2 * Cc[s].get(l - 1, 0) * c[(s, j)] for s in range(1, A + 1) for j in range(n + 1)), 0 * unit)
    P[0] = -sum((c[(s, j)] * Wfun(n, qq, s, j, unit) for s in range(1, A + 1) for j in range(n + 1)), 0 * unit)
    Q0 = sum((c[(s, j)] for s in range(1, A + 1) for j in range(n + 1)), 0 * unit)
    return P, Q0


def is_int_laurent(f):
    if f == 0:
        return True
    den = f.denom
    if len(den.terms()) != 1:
        return False
    (mon, dc), = den.terms()
    if mon[1] != 0:
        return False
    for m, cf in f.numer.terms():
        if m[1] != 0:
            return False
        v = cf / dc
        if v.denominator != 1:
            return False
    return True


def dn(n, qq):
    x = symbols('x')
    p = one
    for l in range(1, n + 1):
        cp = Poly(cyclotomic_poly(l, x), x).all_coeffs()[::-1]
        p *= sum((int(a) * qq**i for i, a in enumerate(cp)), 0 * one)
    return p


def run(A, r, n):
    e = (A - 2 * r) * n // 2
    out = {}
    Rt = R(A, r, n, T, q)
    out['wp'] = R(A, r, n, q**(-n) / T, q) == q**(A * n // 2) * T**A * Rt
    out['inv'] = R(A, r, n, T, 1 / q) == q**(-e) * R(A, r, n, q**(-n) * T, q)
    c = coeffs(A, r, n, q, one)
    pf = sum((c[(s, j)] / (1 - q**j * T)**s for s in range(1, A + 1) for j in range(n + 1)), 0 * one)
    out['pf'] = (pf == Rt)
    ci = coeffs(A, r, n, 1 / q, one)
    out['cinv'] = all(ci[(s, j)] == q**(-e) * c[(s, n - j)] for s in range(1, A + 1) for j in range(n + 1))
    d = dn(n, q)
    out['den'] = all(is_int_laurent(d**(A - s) * c[(s, j)]) for s in range(1, A + 1) for j in range(n + 1))
    P, Q0 = forms(A, r, n, c, q, one)
    Pi, _ = forms(A, r, n, ci, 1 / q, one)
    out['Q0'] = (Q0 == 0)
    out['recip'] = all(Pi[l] == q**(-e) * P[l] for l in P if l > 0) and Pi[0] == -q**(-e) * P[0]
    F = factorial(A - 1)
    out['dgen'] = all(is_int_laurent(F * d**(A - l) * P[l]) for l in P if l > 0) and is_int_laurent(d**A * P[0])
    out['info_noFact'] = all(is_int_laurent(d**(A - l) * P[l]) for l in P if l > 0)
    out['info_dA-1_P0'] = is_int_laurent(d**(A - 1) * P[0])
    Tot = sum(int(totient(l)) for l in range(1, n + 1))
    out['dsym'] = dn(n, 1 / q) == -q**(-Tot) * d
    return out


if __name__ == "__main__":
    triples = [(4, 1, 1), (4, 1, 2), (4, 1, 3), (6, 1, 2), (6, 2, 2), (8, 1, 1), (8, 2, 2), (8, 3, 1), (10, 2, 1),
               (12, 2, 1)]
    if len(sys.argv) > 1:
        triples = [tuple(map(int, a.split(','))) for a in sys.argv[1:]]
    for t in triples:
        res = run(*t)
        print(t, res, flush=True)
