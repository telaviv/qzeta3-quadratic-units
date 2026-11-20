"""Final referee: the numbers of Theorem 1.1, Corollary 1.2, Remark 8.5 and Section 7 (mpmath, 50 digits; exact
rational/sympy algebra where an identity is claimed)."""
import mpmath as mp
import sympy as sp

mp.mp.dps = 50
pi = mp.pi


def tau(A, r):
    return (4 * pi**2 * r * (A - 2 * r) - 12 * A) / (12 * A + pi**2 * (A + 4 * r**2))


def tau_unbal(A, r):
    return (4 * pi**2 * r * (A - 2 * r) - 24 * A) / (24 * A + pi**2 * (A + 4 * r**2))


print("1+tau(4,1) =", mp.nstr(1 + tau(4, 1), 12))
print("1+tau(12,2) =", mp.nstr(1 + tau(12, 2), 12), " formula (64pi^2-144)/(144+28pi^2) =",
      mp.nstr((64 * pi**2 - 144) / (144 + 28 * pi**2), 12))
for A in (6, 8, 10, 12):
    print("A=%d best r:" % A, max(((mp.nstr(1 + tau(A, r), 8), r) for r in range(1, A // 2)), key=lambda x: float(x[0])))
print("const pi/sqrt(12+pi^2) =", mp.nstr(pi / mp.sqrt(12 + pi**2), 12), " t* =", mp.nstr(mp.sqrt(12 + pi**2) / (2 * pi), 10))
print("unbalanced const pi/sqrt(24+pi^2) =", mp.nstr(pi / mp.sqrt(24 + pi**2), 12),
      " KRZ const pi/(2 sqrt(12+pi^2)) =", mp.nstr(pi / (2 * mp.sqrt(12 + pi**2)), 12))
print("unbalanced 1+tau at (4,1) =", mp.nstr(1 + tau_unbal(4, 1), 8))
print("12/pi^2 - 2 =", mp.nstr(12 / pi**2 - 2, 10))

# symbolic identities
A, r, P = sp.symbols('A r pi', positive=True)
dec = r * (A - 2 * r) / 2
deg = 3 * A / P**2
coef = (A + 4 * r**2) / 8
alpha = deg / 2 - dec
beta = deg / 2 + coef
tau_s = (4 * P**2 * r * (A - 2 * r) - 12 * A) / (12 * A + P**2 * (A + 4 * r**2))
print("1-alpha/beta == 1+tau :", sp.simplify(1 - alpha / beta - (1 + tau_s)) == 0)
print("1+tau == (dec+coef)/(deg/2+coef):", sp.simplify((dec + coef) / (deg / 2 + coef) - (1 + tau_s)) == 0)
krz = (4 * r * A + A - 4 * r**2) / ((24 / P**2 + 2) * A + 8 * r**2)   # KRZ (3.4)
print("KRZ (3.4) == (dec+coef)/(deg+2coef):", sp.simplify(krz - (dec + coef) / (deg + 2 * coef)) == 0)
print("1+tau == 2*KRZ(3.4):", sp.simplify(1 + tau_s - 2 * krz) == 0)
print("KRZ delta(12,2) =", sp.N(krz.subs({A: 12, r: 2, P: sp.pi}), 10))
alpha_u = deg - dec
beta_u = deg + coef
tau_u = (4 * P**2 * r * (A - 2 * r) - 24 * A) / (24 * A + P**2 * (A + 4 * r**2))
print("unbalanced 1-alpha/beta == stated:", sp.simplify(1 - alpha_u / beta_u - (1 + tau_u)) == 0)
print("alpha>=0 <=> tau<=0 (numerators):", sp.simplify(-8 * P**2 * alpha - (4 * P**2 * r * (A - 2 * r) - 12 * A)) == 0)
# asymptotic
t = sp.symbols('t', positive=True)
lim = sp.limit(tau_s.subs(r, t * sp.sqrt(A)) / sp.sqrt(A), A, sp.oo)
print("lim tau(A,t sqrt A)/sqrt A =", sp.simplify(lim))
crit = sp.solve(sp.diff(lim, t), t)
print("critical t:", crit, " value:", [sp.simplify(lim.subs(t, c)) for c in crit])
# admissibility of r = ceil(t* sqrt A)
ts = mp.sqrt(12 + pi**2) / (2 * pi)
bad = [a for a in range(4, 200001, 2) if not (1 <= int(mp.ceil(ts * mp.sqrt(a))) < a / 2)]
print("even A in [4, 2e5] with ceil(t* sqrt A) not admissible:", bad)
# sqrt d independence: Corollary-type thresholds
thr = {}
for k in range(2, 9):
    for a in range(4, 400, 2):
        if max(1 + tau(a, rr) for rr in range(1, a // 2)) > k:
            thr[k] = a
            break
print("smallest A with 1+tau > k-? (dim >= k):", thr)

# Section 7: elementary totient bound and its claimed closed forms
from sympy import totient
ok = True
for n in range(1, 3001):
    Tn = sum(int(totient(l)) for l in range(1, n + 1)) if n < 50 else None
ok_list = []
Tn = 0
for n in range(1, 20001):
    Tn += int(totient(n))
    odd = ((n + 1) // 2) ** 2
    half = (n // 2) * (n // 2 + 1) // 2
    ok_list.append(Tn <= odd + half and 8 * (odd + half) <= 3 * n * n + 6 * n + 2 and 8 * Tn <= 3 * (n + 1) ** 2)
print("Tot(n) <= sum_odd + sum_half <= (3n^2+6n+2)/8 <= 3(n+1)^2/8 for n<=20000:", all(ok_list))
print("Tot(20000)/20000^2 =", Tn / 20000**2, " 3/pi^2 =", float(3 / pi**2))
