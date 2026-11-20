"""Final referee: the explicit bound of Lemma 9.2 (coefficients) against c_{s,j}(q) computed numerically,
and the derived P_l, P_0 bounds, at real q of both signs (including units) and a complex q."""
import mpmath as mp
import f_sym as F

mp.mp.dps = 80


def check(A, r, n, qn):
    kap = abs(qn)
    rho = (1 - kap) / 2
    cplus = mp.nprod(lambda i: 1 + kap**i, [1, mp.inf])
    c3 = mp.nprod(lambda i: 1 - (1 + rho) * kap**i, [1, mp.inf])
    c4 = mp.nprod(lambda i: 1 + (1 + rho) * kap**i, [1, mp.inf])
    e = (A - 2 * r) * n // 2
    c = F.coeffs(A, r, n, qn, mp.mpf(1) if not isinstance(qn, mp.mpc) else mp.mpc(1))
    worst = -mp.inf
    for j in range(n + 1):
        E = mp.mpf(A) / 2 * j * (n - j) - mp.mpf(A) / 2 * j + mp.mpf(r * r * n * n) / 2 + mp.mpf(r * n) / 2
        for s in range(1, A + 1):
            bound = rho**(s - A * (j + 1)) * cplus**(A - 2 * r + 1) * c4 * c3**(-A) * (1 + rho)**(r * n + e) * kap**(-E)
            ratio = abs(c[(s, j)]) / bound
            worst = max(worst, ratio)
    return worst


phi = (1 + mp.sqrt(5)) / 2
qs = {"phi^-2": phi**-2, "-phi^-2": -phi**-2, "2-sqrt3": 2 - mp.sqrt(3), "-(3-2sqrt2)": -(3 - 2 * mp.sqrt(2)),
      "0.9": mp.mpf('0.9'), "-0.9": mp.mpf('-0.9'), "0.5i+0.3": mp.mpc('0.3', '0.5')}
for (A, r, n) in [(4, 1, 6), (6, 1, 4), (6, 2, 4), (8, 2, 3), (12, 2, 2)]:
    for name, qn in qs.items():
        w = check(A, r, n, qn)
        print((A, r, n), name, "max |c|/bound = %s" % mp.nstr(w, 4), "OK" if w <= 1 else "FAIL", flush=True)
