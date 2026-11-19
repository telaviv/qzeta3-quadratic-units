import QZeta3.Defs

/-!
# The ingredients, as frozen statements

Numbering: `handoff/fibzeta/many/PROOF_T1.md` (A = 4, r = 1).

* `PFIdentity` — the partial-fraction decomposition (2.1) of `R_n`, with the coefficients `cc`.
* `Expansion` — Lemma 4: `S_n = P₀ + P₃ ζ_q(3)` for real `0 < |q| < 1`. Proved from `PFIdentity`.
* `Recip` — Corollary of Lemma 2 and Lemma 5: `P₃(1/q) = q^{−n} P₃(q)`, `P₀(1/q) = −q^{−n} P₀(q)`.
* `Integrality` — Lemma 3 and §7: `d_n⁴ P₀` and `d_n⁴ P₃` are integer Laurent polynomials in `q`.
* `SizeBound` — Lemmas 1 and 6: `S_n ≠ 0` and `|S_n| ≤ C |q|^{n(n+1)}` for large `n`.
* `CostBound` — Lemma 7, in the weak form that suffices:
  `|d_n(q) d_n(1/q)| ≤ C^{n/8} |q|^{−3(n+1)²/8}` (from `Σ_{ℓ≤n} φ(ℓ) ≤ 3(n+1)²/8`; any constant
  below `1/2` works, so `3/π²` is not needed).
-/

open Polynomial Finset

namespace QZeta3

/-- (2.1): partial fractions of `R_n`, at every real `T` that is not a pole. -/
def PFIdentity : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ q : ℝ, q ≠ 0 → |q| ≠ 1 → ∀ T : ℝ, (∀ j ∈ range (n + 1), q ^ j * T ≠ 1) →
    Rfun n q T = ∑ j ∈ range (n + 1), ∑ s ∈ Icc 1 4, cc n q s j / (1 - q ^ j * T) ^ s

/-- Lemma 4 (the bilateral expansion), A = 4. -/
def Expansion : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ q : ℝ, q ≠ 0 → |q| < 1 → Sn n q = P0 n q + P3 n q * zetaq3 q

/-- Lemma 5 (reciprocity), with `k = n`. -/
def Recip : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ q : ℝ, q ≠ 0 → |q| ≠ 1 →
    P3 n q⁻¹ = (q ^ n)⁻¹ * P3 n q ∧ P0 n q⁻¹ = -((q ^ n)⁻¹ * P0 n q)

/-- Lemma 3 and §7 (denominators). -/
def Integrality : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    LaurentInt (fun x => dn n x ^ 4 * P0 n x) ∧ LaurentInt (fun x => dn n x ^ 4 * P3 n x)

/-- Lemma 6 (size and nonvanishing), r = 1, e = n. -/
def SizeBound : Prop :=
  ∀ q : ℝ, q ≠ 0 → |q| < 1 → ∃ C : ℝ, ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
    Sn n q ≠ 0 ∧ |Sn n q| ≤ C * |q| ^ (n * (n + 1))

/-- Lemma 7 (cyclotomic norms), weak form with constant `3/8 < 1/2`. -/
def CostBound : Prop :=
  ∀ q : ℝ, q ≠ 0 → |q| < 1 → ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
    |dn n q * dn n q⁻¹| ^ 8 ≤ C ^ n * (|q|⁻¹) ^ (3 * (n + 1) ^ 2)

end QZeta3
