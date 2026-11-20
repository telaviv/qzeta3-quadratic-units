"""Final referee: numerical remarks of Section 7 (A=4, r=1).
(1) Q(n) = (log|N delta_n| + 2 log|S_n| + n nu)/(n^2 nu), 6<=n<=30, at q = phi^-2 and -phi^-2 (paper: [-0.82,-0.58]
    and [-0.84,-0.72], oscillating around 12/pi^2 - 2).
(2) log|P_0| / (n^2 nu) at n = 12 for several units (paper: in [0.91, 0.95] for six q).
"""
import mpmath as mp
from sympy import cyclotomic_poly, Poly, symbols
import f_sym as F

mp.mp.dps = 120
x = symbols('x')
CYC = {l: [int(a) for a in Poly(cyclotomic_poly(l, x), x).all_coeffs()[::-1]] for l in range(1, 40)}


def dnv(n, qn):
    p = mp.mpf(1)
    for l in range(1, n + 1):
        p *= mp.fsum(a * qn**i for i, a in enumerate(CYC[l]))
    return p


def Rnum(n, Tn, qn):
    def qp(a, m):
        p = mp.mpf(1)
        for i in range(m):
            p *= (1 - a * qn**i)
        return p
    return qp(qn, n)**2 * qp(qn**(-n) * Tn, n) * qp(qn**(n + 1) * Tn, n) * Tn**n / qp(Tn, n + 1)**4


def Sn(n, qn):
    return mp.fsum(Rnum(n, qn**k, qn) - Rnum(n, qn**(-n - k), qn) for k in range(n + 1, n + 400))


def P0num(n, qn):
    c = F.coeffs(4, 1, n, qn, mp.mpf(1))
    tot = mp.mpf(0)
    for j in range(n + 1):
        for s in range(1, 5):
            W = mp.fsum(1 / (1 - qn**m)**s - 1 for m in range(1, j + 1)) - mp.fsum(1 / (1 - qn**(-m))**s for m in range(1, n - j + 1))
            tot -= c[(s, j)] * W
    return tot


phi = (1 + mp.sqrt(5)) / 2
units = {"phi^-2": phi**-2, "-phi^-2": -phi**-2, "2-sqrt3": 2 - mp.sqrt(3), "-(2-sqrt3)": -(2 - mp.sqrt(3)),
         "3-2sqrt2": 3 - 2 * mp.sqrt(2), "-(3-2sqrt2)": -(3 - 2 * mp.sqrt(2)), "(5-sqrt21)/2": (5 - mp.sqrt(21)) / 2}
for name in ("phi^-2", "-phi^-2"):
    qn = units[name]
    nu = -mp.log(abs(qn))
    vals = []
    for n in range(6, 31):
        Nd = dnv(n, qn) * dnv(n, 1 / qn)
        Q = (4 * mp.log(abs(Nd)) + 2 * mp.log(abs(Sn(n, qn))) + n * nu) / (n * n * nu)
        vals.append(float(Q))
    print(name, "Q(n), n=6..30: min %.4f max %.4f mean %.4f" % (min(vals), max(vals), sum(vals) / len(vals)))
    print("   ", [round(v, 3) for v in vals])
for name, qn in units.items():
    nu = -mp.log(abs(qn))
    p0 = P0num(12, qn)
    print(name, "log|P0(12)|/(144 nu) = %.4f" % float(mp.log(abs(p0)) / (144 * nu)))
