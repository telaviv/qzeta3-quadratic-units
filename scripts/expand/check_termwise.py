"""Exact checks of the termwise identities used in QZeta3/Expand (fractions.Fraction).

fS(s,y) - gS(s,y) = 2 y/(1-y) + aS(s) y(1+y)/(1-y)^3, aS = 0,0,1,2 for s = 1..4,
and sum_{i>=1} i^2 r^i = r(1+r)/(1-r)^3 (partial sums, exact tail-free check via the recursion).
"""
from fractions import Fraction as Fr

aS = {1: 0, 2: 0, 3: 1, 4: 2}
for y in [Fr(2, 7), Fr(-3, 5), Fr(1, 3), Fr(-1, 11), Fr(5, 2)]:
    for s in range(1, 5):
        f = 1 / (1 - y) ** s - 1
        g = 1 / (1 - 1 / y) ** s
        rhs = 2 * y / (1 - y) + aS[s] * y * (1 + y) / (1 - y) ** 3
        assert f - g == rhs, (y, s)
# S(1-r) relation: sum_{i<=N} i^2 r^i = r(1+r)/(1-r)^3 - tail, tail -> 0
r = Fr(1, 3)
N = 200
part = sum(Fr(i * i) * r ** i for i in range(1, N + 1))
assert abs(float(part - r * (1 + r) / (1 - r) ** 3)) < 1e-60
print("termwise identities OK")
