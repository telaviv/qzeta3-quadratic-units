"""Referee misc checks.
M1  Phi(n) = sum_{l<=n} phi(l) <= (3n^2+6n+2)/8 <= 3(n+1)^2/8, and the intermediate bound, for n <= 200000 (exact integers)
M2  Lucas identity sum m^2 (U_{m+1}/U_m - eta) = sqrt(D) zeta_q(3), q = Q/eta^2; Fibonacci second form; Pell (mpmath, 60 digits)
M3  Corollary vs Theorem coverage: is every norm-+1 unit q, 0<|q|<1, of the form Q/eta^2 (Q = +-1, eta a unit)?
    Test K = Q(sqrt3): q = 2 - sqrt3.
M4  Exponent bookkeeping in Main.lean comment / paper Section 7: 4*(3/8)(n+1)^2 - 2 n(n+1) + n.
"""
import mpmath as mp
from sympy import totient

# M1
N = 200000
phi = [0] * (N + 1)
for i in range(N + 1):
    phi[i] = i
for p in range(2, N + 1):
    if phi[p] == p:
        for k in range(p, N + 1, p):
            phi[k] -= phi[k] // p
Phi = 0
ok = True
ok_mid = True
worst = 0.0
for n in range(1, N + 1):
    Phi += phi[n]
    odd_sum = ((n + 1) // 2) ** 2
    half = (n // 2) * (n // 2 + 1) // 2
    if not (Phi <= odd_sum + half):
        ok_mid = False
    if not (8 * Phi <= 3 * n * n + 6 * n + 2 <= 3 * (n + 1) ** 2):
        ok = False
    worst = max(worst, Phi / (n + 1) ** 2)
print(f"M1 Phi bound n<= {N}: {'OK' if ok else 'FAIL'}; intermediate (odd-sum + half-sum) {'OK' if ok_mid else 'FAIL'}; max Phi/(n+1)^2 = {worst:.5f} (3/8 = 0.375)")
# phi(2m) <= m
print("M1b phi(2m) <= m for m <= 100000:", all(phi[2 * m] <= m for m in range(1, 100001)))

# M2
mp.mp.dps = 60


def zeta3(q):
    return mp.nsum(lambda m: m**2 * q**m / (1 - q**m), [1, mp.inf])


def lucas_sum(P, Q, M=4000):
    U0, U1 = 0, 1
    eta = (P + mp.sqrt(P * P - 4 * Q)) / 2
    tot = mp.mpf(0)
    for m in range(1, M):
        U2 = P * U1 - Q * U0
        t = mp.mpf(m)**2 * (mp.mpf(U2) / U1 - eta)
        tot += t
        U0, U1 = U1, U2
        if m > 50 and abs(t) < mp.mpf(10)**(-70):
            break
    return tot, eta


for (P, Q) in [(1, -1), (2, -1), (3, -1), (5, -1), (3, 1), (4, 1), (7, 1)]:
    S, eta = lucas_sum(P, Q)
    D = P * P - 4 * Q
    q = Q / eta**2
    rhs = mp.sqrt(D) * zeta3(q)
    print(f"M2 (P,Q)=({P},{Q}): |lhs - sqrt(D) zeta_q(3)| = {mp.nstr(abs(S - rhs), 3)}   value = {mp.nstr(S, 20)}")
# Fibonacci second form
phi_ = (1 + mp.sqrt(5)) / 2
F = [0, 1]
for _ in range(400):
    F.append(F[-1] + F[-2])
alt = mp.fsum((-1)**m * mp.mpf(m)**2 / (phi_**m * F[m]) for m in range(1, 400))
S, _ = lucas_sum(1, -1)
print(f"M2 Fibonacci second form: diff = {mp.nstr(abs(S - alt), 3)}")

# M3: in Z[sqrt3] (= O_K for K = Q(sqrt3)) units are +-(2+sqrt3)^k; q = 2 - sqrt3 = (2+sqrt3)^-1.
# Q/eta^2 with eta = +-(2+sqrt3)^k gives +-(2+sqrt3)^{-2k}: even exponents only. So q = (2+sqrt3)^{-1} is NOT covered.
print("M3 q = 2 - sqrt3 has N(q) = (2-sqrt3)(2+sqrt3) =", (2 - mp.sqrt(3)) * (2 + mp.sqrt(3)),
      "; units of Z[sqrt3] are +-(2+sqrt3)^k, so Q/eta^2 = +-(2+sqrt3)^(-2k): odd powers not reached.")

# M4
import sympy as sp
n = sp.symbols('n')
print("M4 exponent:", sp.expand(4 * sp.Rational(3, 8) * (n + 1)**2 - 2 * n * (n + 1) + n))
