"""Referee exact checks in the field Q(q) using sympy's sparse rational-function field (fast).

For each (A, r, n):
  C1 wp       R(q^-n/T) = q^{An/2} T^A R(T)          checked in Q(q)(T) via field("q,T")
  C2 inv      R(T;1/q) = q^-e R(q^-n T; q)
  C3 pf       R(T) = sum c_{s,j} (1-q^j T)^-s        (c_{s,j} := [u^{A-s}] u^A R at T = q^-j (1-u))
  C4 sum c = 0
  C5 cinv     c_{s,j}(1/q) = q^-e c_{s,n-j}(q)
  C6 den      d_n^{A-s} c_{s,j} in Z[q, 1/q]
  C7 W        W_{s,n-j}(1/q) = -W_{s,j}(q) - n
  C8 recip    P_l(1/q) = q^-e P_l, P_0(1/q) = -q^-e P_0 ; Q_0 = 0
  C9 (A=4)    P_3 = sum_j (c_{3,j} + 2 c_{4,j}); d_n P_3, d_n^4 P_0 in Z[q,1/q]; (info) d_n^3 P_0
"""
import sys
from sympy import QQ, ZZ, cyclotomic_poly, binomial, Rational, symbols, Poly, expand_func
from sympy.polys.fields import field

K, q, T = field("q,T", QQ)
one = K(1)


def qpoch(a, m):
    p = one
    for i in range(m):
        p *= (1 - a * q**i)
    return p


def R(A, r, n, TT, qq):
    e = (A - 2 * r) * n // 2
    def qp(a, m):
        p = one
        for i in range(m):
            p *= (1 - a * qq**i)
        return p
    return qp(qq, n)**(A - 2 * r) * qp(qq**(-r * n) * TT, r * n) * qp(qq**(n + 1) * TT, r * n) * TT**e / qp(TT, n + 1)**A


def sub_q_inv(f):
    # f in K (no T dependence) -> f(1/q)
    num, den = f.numer, f.denom
    return K(num.compose(q.numer.ring.gens[0], 1 / q) if False else 0) if False else f.subs(q, 1 / q) if hasattr(f, 'subs') else None


def inv_q(f):
    """f(q,T) -> f(1/q, T) using evaluation of numerator/denominator polynomials."""
    nu = f.numer.as_expr()
    de = f.denom.as_expr()
    from sympy import Symbol
    qs, Ts = symbols('q T')
    return K.from_expr(nu.subs(qs, 1 / qs)) / K.from_expr(de.subs(qs, 1 / qs))


def subsT(f, val):
    from sympy import symbols as S
    qs, Ts = S('q T')
    return K.from_expr(f.numer.as_expr().subs(Ts, val.as_expr())) / K.from_expr(f.denom.as_expr().subs(Ts, val.as_expr()))


# truncated power series in u with coefficients in K
def smul(a, b, M):
    c = [K(0)] * M
    for i in range(M):
        if a[i] == 0:
            continue
        for j in range(M - i):
            if b[j] != 0:
                c[i + j] += a[i] * b[j]
    return c


def sinv(a, M):
    c = [K(0)] * M
    c[0] = 1 / a[0]
    for k in range(1, M):
        c[k] = -sum((a[i] * c[k - i] for i in range(1, k + 1)), K(0)) / a[0]
    return c


def lin(y, j, M):  # 1 - y T, T = q^-j (1 - u)
    t = y * q**(-j)
    return [1 - t, t] + [K(0)] * (M - 2)


def pf(A, r, n):
    M = A
    e = (A - 2 * r) * n // 2
    c = {}
    for j in range(n + 1):
        num = [qpoch(q, n)**(A - 2 * r)] + [K(0)] * (M - 1)
        for i in range(r * n):
            num = smul(num, lin(q**(-r * n) * q**i, j, M), M)
            num = smul(num, lin(q**(n + 1) * q**i, j, M), M)
        Ts = [q**(-j), -q**(-j)] + [K(0)] * (M - 2)
        for _ in range(e):
            num = smul(num, Ts, M)
        den = [one] + [K(0)] * (M - 1)
        for jp in range(n + 1):
            if jp != j:
                f = lin(q**jp, j, M)
                for _ in range(A):
                    den = smul(den, f, M)
        G = smul(num, sinv(den, M), M)
        for s in range(1, A + 1):
            c[(s, j)] = G[A - s]
    return c


def dn(n):
    qs = symbols('q')
    p = 1
    for l in range(1, n + 1):
        p *= cyclotomic_poly(l, qs)
    return K.from_expr(p)


def int_laurent(f):
    de = Poly(f.denom.as_expr(), symbols('q'))
    nu = Poly(f.numer.as_expr(), symbols('q'))
    if len(de.terms()) != 1:
        return False
    cd = de.terms()[0][1]
    return all(Rational(cf, 1) / cd == int(Rational(cf, 1) / cd) for _, cf in nu.terms())


def Cpoly(s):
    x = symbols('x')
    return Poly(expand_func(binomial(x + s - 1, s - 1)), x)


def W(n, s, j, qq):
    return sum((((1 - qq**m)**(-s) - 1) for m in range(1, j + 1)), K(0)) - sum(((1 - qq**(-m))**(-s) for m in range(1, n - j + 1)), K(0))


def run(A, r, n):
    e = (A - 2 * r) * n // 2
    out = []
    Rt = R(A, r, n, T, q)
    out.append(('C1wp', R(A, r, n, q**(-n) / T, q) == q**(A * n // 2) * T**A * Rt))
    out.append(('C2inv', R(A, r, n, T, 1 / q) == q**(-e) * R(A, r, n, q**(-n) * T, q)))
    c = pf(A, r, n)
    pfs = sum((c[(s, j)] / (1 - q**j * T)**s for s in range(1, A + 1) for j in range(n + 1)), K(0))
    out.append(('C3pf', pfs == Rt))
    out.append(('C4sum0', sum(c.values(), K(0)) == 0))
    out.append(('C5cinv', all(inv_q(c[(s, j)]) == q**(-e) * c[(s, n - j)] for s in range(1, A + 1) for j in range(n + 1))))
    d = dn(n)
    out.append(('C6den', all(int_laurent(d**(A - s) * c[(s, j)]) for s in range(1, A + 1) for j in range(n + 1))))
    out.append(('C7W', all(inv_q(W(n, s, n - j, q)) == -W(n, s, j, q) - n for s in range(1, A + 1) for j in range(n + 1))))
    # Q(x) coefficients
    Qc = [K(0)] * A
    for s in range(1, A + 1):
        cp = Cpoly(s)
        cs = sum((c[(s, j)] for j in range(n + 1)), K(0))
        for (deg,), cf in cp.terms():
            Qc[deg] += cs * K(QQ(cf.p, cf.q))
    P = {l: 2 * Qc[l - 1] for l in range(3, A, 2)}
    P0 = -sum((c[(s, j)] * W(n, s, j, q) for s in range(1, A + 1) for j in range(n + 1)), K(0))
    out.append(('Q0=0', Qc[0] == 0))
    out.append(('C8Pl', all(inv_q(P[l]) == q**(-e) * P[l] for l in P)))
    out.append(('C8P0', inv_q(P0) == -q**(-e) * P0))
    if A == 4:
        out.append(('C9P3form', P[3] == sum((c[(3, j)] + 2 * c[(4, j)] for j in range(n + 1)), K(0))))
        out.append(('C9dP3', int_laurent(d * P[3])))
        out.append(('C9d4P0', int_laurent(d**4 * P0)))
        out.append(('(info)d3P0', int_laurent(d**3 * P0)))
    return out


if __name__ == '__main__':
    cases = [tuple(map(int, a.split(','))) for a in sys.argv[1:]] or [(4, 1, 1), (4, 1, 2), (4, 1, 3)]
    for cs in cases:
        res = run(*cs)
        print(cs, ' '.join(f"{k}:{'OK' if v else 'FAIL'}" for k, v in res), flush=True)
