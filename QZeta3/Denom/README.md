# QZeta3/Denom: `integrality : Integrality`

PROOF_T1 §2 Lemma 3 (denominators of the partial-fraction coefficients) and the two integrality
bullets of §7, with A = 4, r = 1.

| file | content | PROOF_T1 |
|---|---|---|
| `Laurent.lean` | `LaurentInt` closure (`QZeta3.LaurentInt.add/mul/neg/sub/pow/sum/prod/congr`, constants, `x`, `x⁻¹`); facts about admissible `x` (`x^m ≠ 1`, `m ↦ x^m` injective) | – |
| `Cyclo.lean` | `dn_laurent`, `dn_div` (`d_n/(1 − x^m)`), `dn_div_inv` (`d_n/(1 − x^{−m})`), `dn_div_ratio` (`d_n/(1 − x^{a−b})`) via `∏_{ℓ∣m} Φ_ℓ = X^m − 1` | §2, before Lemma 3 |
| `Gauss.lean` | Gaussian binomials `gauss n k ∈ ℤ[X]` (q-Pascal) and `gauss_mul`: `(x;x)_k (x;x)_m [k+m,k] = (x;x)_{k+m}` | Lemma 3, "Gaussian binomial" |
| `Lagrange.lean` | simple partial fractions `lagrange` of a polynomial of degree ≤ n at the nodes `x^{−j'}`; `den_eq`: `∏_{j''≠j'}(1 − x^{j''−j'}) = U_{j'} (x;x)_{j'} (x;x)_{n−j'}` | Lemma 3, "each f_i is proper with simple poles" |
| `Weights.lean` | the weights `a_{i,j'}` of the three numerators `(x;x)_n`, `(x^{−n}T;x)_n`, `(x^{n+1}T;x)_n` are `±x^{…}`·(one or two Gaussian binomials): `wt_N1`, `wt_N3`, `wt_N4`, hence `LaurentInt` | Lemma 3, the three types |
| `SerInt.lean` | `SerInt n F`: `d_n^K [u^K] F` is `LaurentInt` for all `K`; closure under `+ − ×`, sums, powers; the geometric series `u/(α + βu)` | Lemma 3, "the coefficient of u^M" |
| `Gser.lean` | `Gser_eq`: `Gser = T(u)ⁿ · E(N1)² · E(N3) · E(N4)` (from `N_i(T(u)) = E(N_i) · L`, `Dother = L⁴`); `serInt_Gser` | Lemma 3, last paragraph |
| `Top.lean` | `cc_laurent` (`d_n^{4−s} c_{s,j}`), `Wf_laurent` (`d_n^s W_{s,j}`), **`integrality`** | Lemma 3; §7 bullets |

Uniformity in `x` (one Laurent polynomial for all admissible `x`) is automatic: every object is
shown equal, at each admissible `x`, to an expression built by the closure rules from `x`,
integer polynomials evaluated at `x` (`gauss`, products of cyclotomic polynomials) and `x⁻¹`.

Numerical check of the intermediate identities (exact, `fractions.Fraction`):
`scripts/denom/check_denom.py`.
