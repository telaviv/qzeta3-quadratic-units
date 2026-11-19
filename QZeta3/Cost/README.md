# QZeta3/Cost — Lemma 7 (weak form)

`QZeta3.Cost.costBound : CostBound` (PROOF_T1 §6, Lemma 7, with constant 3/8 in place of 3/π²).

| Lean | PROOF_T1 step |
|---|---|
| `Cyclo.sum_cycErr` | `∑_{a∣n} (log|Φ_a(q)| + log|Φ_a(1/q)| − φ(a) log|q|⁻¹) = 2 log|1 − qⁿ|` (from `∏_{a∣n} Φ_a = Xⁿ − 1`) |
| `Cyclo.abs_cycG_le` | `|2 log|1 − qⁿ|| ≤ 2|q|ⁿ/(1 − |q|)` |
| `Cyclo.abs_cycErr_le` | Möbius inversion: the error per factor is at most `M = 2/(1 − |q|)²`, uniformly in `ℓ` |
| `Cyclo.norm_cyc_le` | `|Φ_ℓ(q) Φ_ℓ(1/q)| ≤ e^M |q|^{−φ(ℓ)}` |
| `Top.totient_two_mul_le`, `Top.eight_sum_totient_le` | `8 ∑_{ℓ≤n} φ(ℓ) ≤ 3(n+1)²` (sieve at 2) |
| `Top.abs_dn_mul_le` | `|d_n(q) d_n(1/q)| ≤ e^{Mn} |q|^{−∑φ}` |
| `Top.costBound` | `|d_n(q) d_n(1/q)|⁸ ≤ (e^{8M})ⁿ |q|^{−3(n+1)²}` |

`Cyclo.lean` is adapted from `lean_lucasu/LucasU/Cost/Cyclo.lean`. Numerical sanity check:
`scripts/cost/check_cost.py`.
