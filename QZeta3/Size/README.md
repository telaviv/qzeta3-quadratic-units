# QZeta3/Size — `SizeBound` (PROOF_T1 Lemmas 1 and 6, A = 4, r = 1, e = n)

Main theorem: `QZeta3.Size.sizeBound : SizeBound` in `Top.lean`, with `C = 3·e^{8K}`, `K = κ/(1−κ)²`, `κ = |q|`.

| file | Lean name | PROOF_T1 step |
|---|---|---|
| `Poch.lean` | `poch_bounds` | §5: for `a ≥ 1`, `e^{−K} ≤ |(q^a;q)_l| ≤ e^K` (stands in for `c₋ ≤ |(q^a;q)_m| ≤ c₊`) |
| `Poch.lean` | `Rfun_pow_eq_zero` | §5: `R(q^m) = 0` for `1 ≤ m ≤ n` |
| `Poch.lean` | `Rfun_pow_bounds` | §5: `e^{−8K} κ^{mn} ≤ |R(q^m)| ≤ e^{8K} κ^{mn}` for `m ≥ n+1` |
| `Symm.lean` | `Rfun_symm` | §1 Lemma 1: `R(q^{−n}T^{−1}) = q^{2n} T⁴ R(T)` (factor by factor: `D_symm`, `A_symm`, `B_symm`, `key_scalar`) |
| `Top.lean` | `Rfun_neg` | Lemma 1 at `T = q^{k+1}` |
| `Top.lean` | `sizeBound` | §5 Lemma 6: `S_n = Σ_{k≥n} (1 − q^{2n+4(k+1)}) R(q^{k+1})`; main term `k = n`, geometric tail with ratio `κ^n` |

`N₀ = max N 1` where `κ^N < (1−κ)e^{−8K}/(4e^{8K})`. Numerical checks: `scripts/size/check_size.py`.
