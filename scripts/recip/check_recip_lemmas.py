# Exact checks (Fractions) of the intermediate identities used in QZeta3/Reciprocity.
from fractions import Fraction as Fr

def qpoch(x, q, m):
    r = Fr(1)
    for i in range(m): r *= (1 - x * q**i)
    return r

def N(n, q, T):
    return qpoch(q, q, n)**2 * qpoch(T / q**n, q, n) * qpoch(q**(n+1) * T, q, n) * T**n

def W(n, q, s, j):
    return sum((1/(1 - q**m)**s - 1) for m in range(1, j+1)) - sum(1/(1 - 1/q**m)**s for m in range(1, n-j+1))

q = Fr(2, 7); V = Fr(3, 11); u = Fr(5, 13)
for n in range(1, 7):
    # N(q^n V; 1/q) = q^-n N(V; q)
    assert N(n, 1/q, q**n * V) == N(n, q, V) / q**n
    # qPoch(1/q;1/q)_n^2 q^{n(n+1)} = (q;q)_n^2
    assert qpoch(1/q, 1/q, n)**2 * q**(n*(n+1)) == qpoch(q, q, n)**2
    for j in range(n+1):
        # Dother factors: (1/q)^j' * q^j  ==  q^(n-j') / q^(n-j)
        for jp in range(n+1):
            assert (1/q)**jp * q**j == q**(n-jp) / q**(n-j)
        for s in range(1, 5):
            assert W(n, 1/q, s, n-j) == -W(n, q, s, j) - n
print("all recip lemma checks passed")
