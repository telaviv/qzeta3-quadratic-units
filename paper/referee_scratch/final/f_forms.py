"""Final referee: the balanced trace forms of Section 8, built exactly in Q(sqrt d) at real quadratic units.

For each (A, r, n) and unit q = (s - f sqrt d)/2 (|q| < 1):
  * Delta_n P_0, Delta_n P_l as integer Laurent polynomials (exact, sympy field; Lemma 8.1);
  * their exact values in Q(sqrt d); balancing exponent m from (8.4); Delta' = q^-m Delta_n;
  * ell_0 = Tr(Delta' P_0), ell_l = Tr(Delta' P_l / sqrt d): integrality (Lemma 8.3(a));
  * Lemma 4.1 at q (S_n direct bilateral sum vs P_0 + sum P_l zeta_q(l));
  * (8.2) sigma P_l = q^-e P_l, sigma P_0 = -q^-e P_0 exactly in Q(sqrt d);
  * Lemma 8.3(b): L_n = (Delta' - q^-e sigma Delta') S_n (mpmath, high precision);
  * |Delta'| <= M_n/2 and M_n^2 / (kappa^-e |Delta sigma Delta|) in [2, 2 kappa^-2).
"""
import sys
from fractions import Fraction as Fr
from math import factorial, isqrt
import mpmath as mp
import f_sym as F

mp.mp.dps = 500


class QD:
    d = 5

    def __init__(self, a, b=0):
        self.a, self.b = Fr(a), Fr(b)

    def __add__(s, o):
        o = o if isinstance(o, QD) else QD(o)
        return QD(s.a + o.a, s.b + o.b)
    __radd__ = __add__

    def __sub__(s, o):
        o = o if isinstance(o, QD) else QD(o)
        return QD(s.a - o.a, s.b - o.b)

    def __mul__(s, o):
        o = o if isinstance(o, QD) else QD(o)
        return QD(s.a * o.a + QD.d * s.b * o.b, s.a * o.b + s.b * o.a)
    __rmul__ = __mul__

    def conj(s):
        return QD(s.a, -s.b)

    def __eq__(s, o):
        o = o if isinstance(o, QD) else QD(o)
        return s.a == o.a and s.b == o.b

    def pw(s, k):
        # s a unit of norm 1 assumed when k < 0
        base = s if k >= 0 else s.conj()
        k = abs(k)
        r = QD(1)
        while k:
            if k & 1:
                r = r * base
            base = base * base
            k >>= 1
        return r

    def num(s):
        return mp.mpf(s.a.numerator) / s.a.denominator + mp.mpf(s.b.numerator) / s.b.denominator * mp.sqrt(QD.d)


def unit_from_s(s):
    D = s * s - 4
    f = 1
    for p in range(isqrt(D), 0, -1):
        if D % (p * p) == 0:
            f = p
            break
    d = D // (f * f)
    sg = 1 if s > 0 else -1
    # q = (s - sg f sqrt d)/2 has |q| < 1
    return d, Fr(s, 2), Fr(-sg * f, 2)


def laurent_value(fe, qv):
    """fe: sympy field element that is an integer Laurent polynomial in q; evaluate exactly at qv (QD)."""
    if fe == 0:
        return QD(0), True
    den = fe.denom
    (mon, dc), = den.terms()
    k = mon[0]
    val = QD(0)
    ok = True
    for m, cf in fe.numer.terms():
        v = cf / dc
        ok = ok and v.denominator == 1
        val = val + QD(Fr(int(v.numerator), int(v.denominator))) * qv.pw(m[0] - k)
    return val, ok


def zeta_q(qn, l, kap):
    M = int(mp.mp.dps * mp.log(10) / -mp.log(kap)) + 50
    return mp.fsum(mp.mpf(m)**(l - 1) * qn**m / (1 - qn**m) for m in range(1, M))


def Rnum(A, r, n, Tn, qn):
    e = (A - 2 * r) * n // 2
    def qp(a, m):
        p = mp.mpf(1)
        for i in range(m):
            p *= (1 - a * qn**i)
        return p
    return qp(qn, n)**(A - 2 * r) * qp(qn**(-r * n) * Tn, r * n) * qp(qn**(n + 1) * Tn, r * n) * Tn**e / qp(Tn, n + 1)**A


def Sn_direct(A, r, n, qn, kap):
    e = (A - 2 * r) * n // 2
    M = int(mp.mp.dps * mp.log(10) / (-mp.log(kap) * e)) + 5
    tot = mp.mpf(0)
    for k in range(1, r * n + M + 10):
        tot += Rnum(A, r, n, qn**k, qn) - Rnum(A, r, n, qn**(-n - k), qn)
    return tot


def run(A, r, n, s):
    d, a0, b0 = unit_from_s(s)
    QD.d = d
    qv = QD(a0, b0)
    qn = qv.num()
    kap = abs(qn)
    nu = -mp.log(kap)
    e = (A - 2 * r) * n // 2
    c = F.coeffs(A, r, n, F.q, F.one)
    P, _ = F.forms(A, r, n, c, F.q, F.one)
    dsym = F.dn(n, F.q)
    Delta = factorial(A - 1) * dsym**A
    vals = {}
    allint = True
    for l in P:
        v, ok = laurent_value(Delta * P[l], qv)
        vals[l] = v
        allint = allint and ok
    Dv, ok = laurent_value(Delta, qv)
    allint = allint and ok
    # (8.2): sigma(Delta P_l) / sigma(Delta) = q^-e P_l etc.  Check sigma(Delta P_l) * Delta = q^-e (Delta P_l) * sigma(Delta)
    qe = qv.pw(-e)
    sig_ok = all(vals[l].conj() * Dv == qe * vals[l] * Dv.conj() for l in P if l > 0) and \
        vals[0].conj() * Dv == QD(-1) * qe * vals[0] * Dv.conj()
    Dn = Dv.num()
    sDn = Dv.conj().num()
    rho = kap**(-e) * abs(sDn) / abs(Dn)
    m = int(mp.floor(mp.log(rho / 2) / (2 * nu)))
    t = kap**(2 * m) * rho
    bal_ok = (2 <= t < 2 / kap**2)
    Dp = qv.pw(-m) * Dv
    Mn = kap**(-e) * abs(Dp.conj().num())
    half_ok = abs(Dp.num()) <= Mn / 2
    # trace forms
    x0 = qv.pw(-m) * vals[0]
    ell = {0: 2 * x0.a}
    for l in P:
        if l > 0:
            x = qv.pw(-m) * vals[l]
            ell[l] = 2 * x.b  # Tr(x/sqrt d) = 2b for x = a + b sqrt d
    int_ok = all(v.denominator == 1 for v in ell.values())
    zs = {l: zeta_q(qn, l, kap) for l in P if l > 0}
    Sd = Sn_direct(A, r, n, qn, kap)
    Pnum = {l: vals[l].num() / Dn for l in P}
    Sexp = Pnum[0] + mp.fsum(Pnum[l] * zs[l] for l in zs)
    exp_err = abs(Sd - Sexp) / abs(Sd)
    Ln = mp.mpf(int(ell[0])) + mp.fsum(mp.mpf(int(ell[l])) * mp.sqrt(d) * zs[l] for l in zs)
    rhs = (Dp.num() - qn**(-e) * Dp.conj().num()) * Sd
    L_err = abs(Ln - rhs) / abs(Ln)
    maxell = max(abs(int(v)) for v in ell.values())
    return dict(A=A, r=r, n=n, s=s, d=d, laurent_int=allint, sigmaP=sig_ok, balance=bal_ok, half=half_ok,
                ell_int=int_ok, exp_relerr=mp.nstr(exp_err, 3), L_relerr=mp.nstr(L_err, 3),
                log10_absL=mp.nstr(mp.log10(abs(Ln)), 6), log10_maxell=mp.nstr(mp.log10(maxell), 6),
                logL_over_n2nu=mp.nstr(mp.log(abs(Ln)) / (n * n * nu), 5),
                pred_alpha=mp.nstr(3 * A / (2 * mp.pi**2) - r * (A - 2 * r) / 2, 5))


if __name__ == "__main__":
    triples = [(4, 1, 2), (4, 1, 4), (6, 1, 2), (6, 2, 2), (8, 2, 2), (8, 3, 1), (12, 2, 1)]
    for t in triples:
        for s in (3, -3, 4, -6):
            print(run(*t, s), flush=True)
