"""Referee exact checks in Q(q) (sympy), independent of the authors' scripts.

Checks, for several (A, r, n):
  C1  Lemma wp:   R(q^-n/T) = q^{An/2} T^A R(T)                       (in Q(q,T))
  C2  Lemma inv:  R(T;1/q) = q^-e R(q^-n T; q)                         (in Q(q,T))
  C3  partial fractions (2.1) with c_{s,j} computed as [u^{A-s}] of u^A R at T=q^-j(1-u)  (in Q(q,T))
  C4  sum c_{s,j} = 0
  C5  Cor cinv:   c_{s,j}(1/q) = q^-e c_{s,n-j}(q)
  C6  Lemma den:  d_n^{A-s} c_{s,j} in Z[q,1/q]
  C7  W identity: W_{s,n-j}(1/q) = -W_{s,j}(q) - n
  C8  Lemma recip: P_l(1/q) = q^-e P_l(q) (odd l>=3), P_0(1/q) = -q^-e P_0(q)
  C9  (A=4) d_n P_3 and d_n^4 P_0 in Z[q,1/q]; also report whether d_n^3 P_0 is.
"""
import sys
import sympy as sp
from sympy import Poly, QQ, ZZ

q, T, u, x = sp.symbols('q T u x')


def qpoch(a, m):
    r = sp.Integer(1)
    for i in range(m):
        r *= (1 - a * q**i)
    return r


def Rfun(A, r, n, TT):
    e = (A - 2 * r) * n // 2
    return qpoch(q, n)**(A - 2 * r) * qpoch(q**(-r * n) * TT, r * n) * qpoch(q**(n + 1) * TT, r * n) * TT**e / qpoch(TT, n + 1)**A


def is_zero(expr):
    return sp.cancel(sp.together(expr)) == 0


def series_coeffs(expr, var, order):
    """coefficients [var^0..var^{order-1}] of a rational function regular at var=0, as cancelled rational functions in q"""
    s = sp.series(expr, var, 0, order).removeO()
    return [sp.cancel(s.coeff(var, k)) for k in range(order)]


def pf_coeffs(A, r, n):
    e = (A - 2 * r) * n // 2
    c = {}
    for j in range(n + 1):
        Tj = q**(-j) * (1 - u)
        # u^A R(T) = T^e * numerator-blocks * prod_{j' != j} (1-q^{j'}T)^{-A} * (u/(1-q^j T))^A, and 1-q^j T = u
        num = qpoch(q, n)**(A - 2 * r) * qpoch(q**(-r * n) * Tj, r * n) * qpoch(q**(n + 1) * Tj, r * n) * Tj**e
        den = sp.Integer(1)
        for jp in range(n + 1):
            if jp != j:
                den *= (1 - q**jp * Tj)**A
        G = num / den
        co = series_coeffs(G, u, A)
        for s in range(1, A + 1):
            c[(s, j)] = co[A - s]
    return c


def dn(n, var=q):
    r = sp.Integer(1)
    for l in range(1, n + 1):
        r *= sp.cyclotomic_poly(l, var)
    return r


def is_int_laurent(expr):
    ex = sp.cancel(sp.together(expr))
    num, den = sp.fraction(ex)
    pn, pd = Poly(num, q), Poly(den, q)
    # den must be +- monomial
    if len(pd.terms()) != 1:
        return False
    cd = pd.terms()[0][1]
    return all(sp.Rational(cf / cd).q == 1 for (_, cf) in pn.terms())


def sub_inv(expr):
    return sp.cancel(sp.together(expr.subs(q, 1 / q)))


def C(s, xx):
    return sp.expand_func(sp.binomial(xx + s - 1, s - 1))


def W(n, s, j, qq):
    return sum(((1 - qq**m)**(-s) - 1) for m in range(1, j + 1)) - sum((1 - qq**(-m))**(-s) for m in range(1, n - j + 1))


def run(A, r, n, full=True):
    e = (A - 2 * r) * n // 2
    out = []
    R = Rfun(A, r, n, T)
    out.append(('C1 wp', is_zero(Rfun(A, r, n, q**(-n) / T) - q**(A * n // 2) * T**A * R)))
    Rinv = R.subs(q, 1 / q)
    out.append(('C2 inv', is_zero(Rinv - q**(-e) * Rfun(A, r, n, q**(-n) * T))))
    c = pf_coeffs(A, r, n)
    pf = sum(c[(s, j)] / (1 - q**j * T)**s for s in range(1, A + 1) for j in range(n + 1))
    out.append(('C3 pf', is_zero(R - pf)))
    out.append(('C4 sum c = 0', is_zero(sum(c.values()))))
    out.append(('C5 cinv', all(is_zero(sub_inv(c[(s, j)]) - q**(-e) * c[(s, n - j)]) for s in range(1, A + 1) for j in range(n + 1))))
    d = dn(n)
    out.append(('C6 den', all(is_int_laurent(d**(A - s) * c[(s, j)]) for s in range(1, A + 1) for j in range(n + 1))))
    out.append(('C7 W', all(is_zero(W(n, s, n - j, 1 / q) + W(n, s, j, q) + n) for s in range(1, A + 1) for j in range(n + 1))))
    Qx = sp.expand(sum(c[(s, j)] * C(s, x) for s in range(1, A + 1) for j in range(n + 1)))
    Qp = Poly(Qx, x)
    P = {}
    for l in range(3, A, 2):
        P[l] = sp.cancel(2 * Qp.coeff_monomial(x**(l - 1)))
    P0 = sp.cancel(-sum(c[(s, j)] * W(n, s, j, q) for s in range(1, A + 1) for j in range(n + 1)))
    ok = all(is_zero(sub_inv(P[l]) - q**(-e) * P[l]) for l in P)
    out.append(('C8 recip P_l', ok))
    out.append(('C8 recip P_0', is_zero(sub_inv(P0) + q**(-e) * P0)))
    out.append(('Q_0 = 0', is_zero(Qp.coeff_monomial(1))))
    if A == 4:
        out.append(('C9 d P3 int', is_int_laurent(d * P[3])))
        out.append(('C9 P3 = sum(c3+2c4)', is_zero(P[3] - sum(c[(3, j)] + 2 * c[(4, j)] for j in range(n + 1)))))
        out.append(('C9 d^4 P0 int', is_int_laurent(d**4 * P0)))
        out.append(('(info) d^3 P0 int', is_int_laurent(d**3 * P0)))
    return out


if __name__ == '__main__':
    cases = [(4, 1, 1), (4, 1, 2), (4, 1, 3), (4, 1, 4), (6, 1, 2), (6, 2, 2), (6, 2, 3), (8, 3, 2)]
    if len(sys.argv) > 1:
        cases = [tuple(map(int, a.split(','))) for a in sys.argv[1:]]
    for (A, r, n) in cases:
        res = run(A, r, n)
        print((A, r, n), ' '.join(f"{k}:{'OK' if v else 'FAIL'}" for k, v in res), flush=True)
