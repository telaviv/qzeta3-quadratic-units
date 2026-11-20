"""Referee numerical checks (mpmath), independent code. A = 4, r = 1 unless stated.

N1  Lemma expansion: direct S_n (bilateral sum) vs P_0 + P_3 zeta_q(3), at q = phi^-2, -phi^-2, 2-sqrt3, -(3-2sqrt2), 0.37, -0.6
N2  Lemma size: log|S_n| + n(n+1) log(1/|q|) stays bounded
N3  bracket (log|N d_n^4| + 2 log|S_n| + n log(1/k)) / (n^2 log(1/k)) with delta_n = d_n^4 exactly, every 6 <= n <= 30
N4  |P_0| growth: log|P_0| / (n^2 log(1/k))
N5  KRZ comparison: paper's S_n vs KRZ S_n^[1] = S_n(q) - q^-n S_n(1/q) with KRZ's summand q^k * q^{-e/2} R(q^k)
"""
import mpmath as mp
import sys

mp.mp.dps = int(__import__("os").environ.get("DPS", "1600"))
A, r = 4, 1


def qpoch(a, qq, m):
    p = mp.mpf(1)
    for i in range(m):
        p *= (1 - a * qq**i)
    return p


def R(n, qq, TT, A=4, r=1):
    e = (A - 2 * r) * n // 2
    return qpoch(qq, qq, n)**(A - 2 * r) * qpoch(qq**(-r * n) * TT, qq, r * n) * qpoch(qq**(n + 1) * TT, qq, r * n) * TT**e / qpoch(TT, qq, n + 1)**A


def Sn_direct(n, qq, extra_T=0):
    # sum_{k>=1} R(q^k) - sum_{k>=1} R(q^{-n-k}); terms vanish for k <= rn on both sides
    # terms with k <= r*n vanish exactly on both sides (factor 1 - q^0); skip them to avoid rounding noise
    tot = mp.mpf(0)
    k = r * n + 1
    while True:
        t1 = R(n, qq, qq**k) * (qq**k)**extra_T
        t2 = R(n, qq, qq**(-n - k)) * (qq**(-n - k))**extra_T
        t = t1 - t2
        tot += t
        if k > r * n + 2 and abs(t) < abs(tot) * mp.mpf(10)**(-mp.mp.dps + 20):
            break
        k += 1
    return tot


def trunc_mul(a, b, M):
    c = [mp.mpf(0)] * M
    for i in range(M):
        if a[i] == 0:
            continue
        for j in range(M - i):
            c[i + j] += a[i] * b[j]
    return c


def trunc_inv(a, M):
    c = [mp.mpf(0)] * M
    c[0] = 1 / a[0]
    for k in range(1, M):
        c[k] = -sum(a[i] * c[k - i] for i in range(1, k + 1)) / a[0]
    return c


def lin(y, qq, j, M):  # 1 - y T with T = q^-j (1-u)
    t = y * qq**(-j)
    return [1 - t, t] + [mp.mpf(0)] * (M - 2)


def pf(n, qq):
    M = A
    e = (A - 2 * r) * n // 2
    c = {}
    for j in range(n + 1):
        num = [qpoch(qq, qq, n)**(A - 2 * r)] + [mp.mpf(0)] * (M - 1)
        for i in range(r * n):
            num = trunc_mul(num, lin(qq**(-r * n) * qq**i, qq, j, M), M)
            num = trunc_mul(num, lin(qq**(n + 1) * qq**i, qq, j, M), M)
        Tser = [qq**(-j), -qq**(-j)] + [mp.mpf(0)] * (M - 2)
        for _ in range(e):
            num = trunc_mul(num, Tser, M)
        den = [mp.mpf(1)] + [mp.mpf(0)] * (M - 1)
        for jp in range(n + 1):
            if jp == j:
                continue
            f = lin(qq**jp, qq, j, M)
            for _ in range(A):
                den = trunc_mul(den, f, M)
        G = trunc_mul(num, trunc_inv(den, M), M)
        for s in range(1, A + 1):
            c[(s, j)] = G[A - s]
    return c


def W(n, s, j, qq):
    return sum(((1 - qq**m)**(-s) - 1) for m in range(1, j + 1)) - sum((1 - qq**(-m))**(-s) for m in range(1, n - j + 1))


def forms(n, qq):
    c = pf(n, qq)
    P3 = sum(c[(3, j)] + 2 * c[(4, j)] for j in range(n + 1))
    P0 = -sum(c[(s, j)] * W(n, s, j, qq) for s in range(1, A + 1) for j in range(n + 1))
    return P0, P3, c


def zeta3(qq):
    tot = mp.mpf(0)
    m = 1
    while True:
        t = mp.mpf(m)**2 * qq**m / (1 - qq**m)
        tot += t
        if abs(t) < mp.mpf(10)**(-mp.mp.dps - 5):
            break
        m += 1
    return tot


def cyclo_vals(n, qq):
    # Phi_l(q) via Moebius product, exact up to precision
    from sympy import mobius, divisors
    v = mp.mpf(1)
    for l in range(1, n + 1):
        p = mp.mpf(1)
        for a in divisors(l):
            p *= (qq**a - 1)**int(mobius(l // a))
        v *= p
    return v


if __name__ == '__main__':
    phi = (1 + mp.sqrt(5)) / 2
    units = {'phi^-2': phi**-2, '-phi^-2': -phi**-2, '2-sqrt3': 2 - mp.sqrt(3), '-(3-2sqrt2)': -(3 - 2 * mp.sqrt(2))}
    nonunits = {'0.37': mp.mpf('0.37'), '-0.6': mp.mpf('-0.6')}
    which = sys.argv[1] if len(sys.argv) > 1 else 'all'
    if which in ('all', 'N1'):
        print('N1 expansion / N2 size / N4 |P0|')
        for name, qq in list(units.items()) + list(nonunits.items()):
            Z = zeta3(qq)
            lk = mp.log(1 / abs(qq))
            for n in (1, 2, 3, 5, 8, 12):
                P0, P3, c = forms(n, qq)
                S = Sn_direct(n, qq)
                L = P0 + P3 * Z
                rel = abs(L - S) / abs(S)
                print(f"  q={name:12s} n={n:2d} relerr={mp.nstr(rel, 3):>10s}  logS+n(n+1)log(1/k)={mp.nstr(mp.log(abs(S)) + n*(n+1)*lk, 6):>9s}"
                      f"  log|P0|/(n^2 log1/k)={mp.nstr(mp.log(abs(P0))/(n*n*lk), 4)}", flush=True)
    if which in ('all', 'N3'):
        print('N3 bracket with delta_n = d_n^4 (exact Norm via d_n(q) d_n(1/q))')
        for name in ('phi^-2', '-phi^-2'):
            qq = units[name]
            lk = mp.log(1 / abs(qq))
            vals = []
            for n in range(6, 31):
                S = Sn_direct(n, qq)
                Nd = cyclo_vals(n, qq) * cyclo_vals(n, 1 / qq)
                Ndr = mp.nint(Nd)
                assert abs(Nd - Ndr) < mp.mpf(10)**(-50), (n, Nd)
                br = (4 * mp.log(abs(Ndr)) + 2 * mp.log(abs(S)) + n * lk) / (n * n * lk)
                br6 = (4 * mp.log(abs(Ndr)) + mp.log(36) + 2 * mp.log(abs(S)) + n * lk) / (n * n * lk)
                vals.append((n, br, br6))
                print(f"  q={name} n={n:2d} bracket(d^4)={mp.nstr(br, 5)}  bracket(6d^4)={mp.nstr(br6, 5)}", flush=True)
            print(f"  q={name}: range d^4: [{mp.nstr(min(v[1] for v in vals),4)}, {mp.nstr(max(v[1] for v in vals),4)}];"
                  f" range 6d^4: [{mp.nstr(min(v[2] for v in vals),4)}, {mp.nstr(max(v[2] for v in vals),4)}]")
    if which in ('all', 'N5'):
        print('N5 KRZ S^[1] (their summand q^k q^{-e/2} R(q^k), KRZ (3.1)ff) vs paper S_n')
        qq = units['phi^-2']
        for n in (2, 4, 6, 8):
            e = n
            S = Sn_direct(n, qq)
            def krz_Sn(qb):
                tot = mp.mpf(0); k = 1
                while True:
                    t = qb**k * qb**(-mp.mpf(e) / 2) * R(n, qb, qb**k)
                    tot += t
                    if k > n + 3 and abs(t) < abs(tot) * mp.mpf(10)**(-300):
                        break
                    k += 1
                return tot
            # S_n(1/q): base 1/q, T = (1/q)^k; terms decay (|q|>... checked by convergence test)
            S1 = krz_Sn(qq) - qq**(-n) * krz_Sn(1 / qq)
            Sk = Sn_direct(n, qq, extra_T=1)
            print(f"  n={n} S_paper={mp.nstr(S,8)}  KRZ S^[1]={mp.nstr(S1,8)}  q^(-e/2)*S(T^(e+1))={mp.nstr(qq**(-mp.mpf(e)/2)*Sk,8)}"
                  f"  log|S_paper/KRZ|/log(1/q)={mp.nstr(mp.log(abs(S/S1))/mp.log(1/qq),6)}", flush=True)
