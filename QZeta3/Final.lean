import QZeta3.Main

/-!
# Main results (frozen statements)

Source: `handoff/fibzeta/many/PROOF_T1.md`, Theorem T1 and its Corollary.

**Theorem T1.** Let `K = ℚ(√d)` be a real quadratic field and `q ∈ O_K^×` a unit of norm `+1`
with `0 < |q| < 1`. Then `√d · ζ_q(3) ∉ ℚ`.

Elementary form used here.
* A real `q` is a unit of norm `+1` in a real quadratic field exactly when `s = q + q⁻¹`
  (its trace) is an integer and `q ∉ ℚ`. With `0 < |q| < 1` we get `|s| > 2`, so `q ∉ ℚ`
  is automatic.
* `K = ℚ(q) = ℚ(√(s² − 4))`, and `K = ℚ(√d)` exactly when `d (s² − 4)` is a square.
* Hence `irrational_sqrt_mul_zetaq3` is T1. It allows any `d > 0` with `d(s² − 4)` a square,
  not only squarefree `d`.
* `irrational_sub_inv_mul_zetaq3` is the same statement with `q − q⁻¹ = ±√(s² − 4)` in place
  of `√d`.

**Corollary.** For every quadratic-unit Lucas sequence, `Σ_{m≥1} m² (U_{m+1}/U_m − ε) ∉ ℚ`.
* Here `U_{m+2} = a U_{m+1} + E U_m` with `E = 1, a ≥ 1` (unit `ε` of norm `−1`) or
  `E = −1, a ≥ 3` (norm `+1`), and `ε = (a + √(a² + 4E))/2`.
* Fibonacci: `Σ m² (F_{m+1}/F_m − φ) ∉ ℚ`.
-/

open Polynomial Finset

namespace QZeta3

/-- **Theorem T1**, elementary form with `θ = q − q⁻¹`. -/
theorem irrational_sub_inv_mul_zetaq3 {q : ℝ} {s : ℤ} (hq0 : q ≠ 0) (hq1 : |q| < 1)
    (hs : q + q⁻¹ = s) : Irrational ((q - q⁻¹) * zetaq3 q) := by
  sorry

/-- **Theorem T1**: `√d · ζ_q(3) ∉ ℚ` for a real quadratic unit `q` of norm `+1`, `0 < |q| < 1`,
with `ℚ(q) = ℚ(√d)`. -/
theorem irrational_sqrt_mul_zetaq3 {q : ℝ} {s : ℤ} (hq0 : q ≠ 0) (hq1 : |q| < 1)
    (hs : q + q⁻¹ = s) {d : ℕ} (hd : 0 < d) (hsq : IsSquare ((d : ℤ) * (s ^ 2 - 4))) :
    Irrational (Real.sqrt d * zetaq3 q) := by
  sorry

/-- **Corollary**: `Σ_{m≥1} m² (U_{m+1}/U_m − ε) ∉ ℚ` for every quadratic-unit Lucas sequence. -/
theorem irrational_lucas_sum {a : ℕ} {E : ℤ} (h : (E = 1 ∧ 1 ≤ a) ∨ (E = -1 ∧ 3 ≤ a)) :
    Irrational (∑' m : ℕ, (m : ℝ) ^ 2 * ((lucasU a E (m + 1) : ℝ) / lucasU a E m - epsU a E)) := by
  sorry

/-- **Corollary, Fibonacci case**: `Σ_{m≥1} m² (F_{m+1}/F_m − φ) ∉ ℚ`. -/
theorem irrational_fib_sum :
    Irrational (∑' m : ℕ, (m : ℝ) ^ 2 * ((Nat.fib (m + 1) : ℝ) / Nat.fib m - Real.goldenRatio)) := by
  sorry

/-- The series defining `ζ_q(3)` converges for `|q| < 1` (so `zetaq3` is not a junk value). -/
theorem summable_zetaq3 {q : ℝ} (hq1 : |q| < 1) :
    Summable (fun m : ℕ => (m : ℝ) ^ 2 * q ^ m / (1 - q ^ m)) := by
  sorry

end QZeta3
