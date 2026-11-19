"""Sanity checks for the cost worker (QZeta3/Cost).

* 8 * sum_{l<=n} phi(l) <= 3 (n+1)^2   (exact, n <= 3000)
* |Phi_l(q) Phi_l(1/q)| <= exp(2/(1-|q|)^2) |q|^{-phi(l)}  (numerical, mpmath, several q)
"""
from math import gcd
import mpmath as mp
from sympy import cyclotomic_poly, totient, Symbol

N = 3000
phi = [0] * (N + 1)
for l in range(1, N + 1):
    phi[l] = int(totient(l))
s = 0
for n in range(1, N + 1):
    s += phi[n]
    assert 8 * s <= 3 * (n + 1) ** 2, n
print("totient sum bound ok up to", N)

mp.mp.dps = 50
x = Symbol("x")
for q in [mp.mpf("0.38196601125"), mp.mpf("-0.9"), mp.mpf("0.97"), mp.mpf("-0.2")]:
    k = abs(q)
    M = 2 / (1 - k) ** 2
    worst = -mp.inf
    for l in range(1, 41):
        c = [int(a) for a in cyclotomic_poly(l, x, polys=True).all_coeffs()]
        v1 = mp.polyval(c, q)
        v2 = mp.polyval(c, 1 / q)
        err = mp.log(abs(v1 * v2)) - phi[l] * mp.log(1 / k)
        assert abs(err) <= M, (q, l, err, M)
        worst = max(worst, abs(err))
    print("q =", mp.nstr(q, 6), "max |F| =", mp.nstr(worst, 6), "bound M =", mp.nstr(M, 6))
