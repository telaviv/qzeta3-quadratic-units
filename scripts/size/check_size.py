# Checks for the size worker's intermediate statements (QZeta3/Size).
#  * Rfun_symm (Lemma 1): R(q^-n T^-1) = q^(2n) T^4 R(T), exact at q = 2/7, -3/5 and several T.
#  * R(q^m) = 0 for 1 <= m <= n (exact).
#  * Rfun_pow_bounds: e^{-8K} k^{mn} <= |R(q^m)| <= e^{8K} k^{mn} for m >= n+1, K = k/(1-k)^2.
#  * sizeBound constants: C = 3 e^{8K}, N0 = max(N, 1) with k^N < (1-k) e^{-8K}/(4 e^{8K}).
from fractions import Fraction as Fr
import math
import mpmath as mp

def qpoch(x, q, m):
    r = 1
    for i in range(m):
        r *= (1 - x * q**i)
    return r

def Rfun(n, q, T):
    return qpoch(q, q, n)**2 * qpoch(q**(-n) * T, q, n) * qpoch(q**(n + 1) * T, q, n) * T**n / qpoch(T, q, n + 1)**4

for q in [Fr(2, 7), Fr(-3, 5)]:
    for n in range(1, 6):
        for T in [Fr(3, 11), Fr(-5, 4), q**2]:
            assert Rfun(n, q, 1 / (q**n * T)) == q**(2 * n) * T**4 * Rfun(n, q, T)
        for m in range(1, n + 1):
            assert Rfun(n, q, q**m) == 0
        k = abs(q)
        K = k / (1 - k)**2
        for m in range(n + 1, n + 8):
            r = abs(Rfun(n, q, q**m)) / k**(m * n)
            assert math.exp(-8 * float(K)) <= r <= math.exp(8 * float(K)), (q, n, m, r)
print("exact Lemma 1, vanishing and Pochhammer bounds OK")

mp.mp.dps = 60
phi = (1 + mp.sqrt(5)) / 2
for q in [phi**-2, -phi**-2]:
    k = abs(q)
    K = k / (1 - k)**2
    E = mp.e**(8 * K)
    for n in range(1, 9):
        S = mp.nsum(lambda j: Rfun(n, q, q**int(j + 1)), [0, 200]) - \
            mp.nsum(lambda j: Rfun(n, q, q**(-(n + int(j) + 1))), [0, 200])
        print(float(q), n, mp.nstr(abs(S) / k**(n * (n + 1)), 8), "<= C =", mp.nstr(3 * E, 6))
        assert abs(S) <= 3 * E * k**(n * (n + 1)) and S != 0
