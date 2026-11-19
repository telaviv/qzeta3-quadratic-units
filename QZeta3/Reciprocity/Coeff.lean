import QZeta3.Statements

/-!
# Reciprocity of the partial-fraction coefficients (PROOF_T1, Corollary of Lemma 2)

`cc n q⁻¹ s j = (q^n)⁻¹ * cc n q s (n − j)` for `j ≤ n`, proved at the level of the power series
`Gser`: the numerator satisfies `N(q^n V; 1/q) = q^{−n} N(V; q)` and the other-pole product
`Dother` is invariant under `(q, j) ↦ (q⁻¹, n − j)`.
-/

open Polynomial Finset

namespace QZeta3.Reciprocity

variable {q : ℝ}

lemma eval_qPochPoly (y q T : ℝ) (m : ℕ) :
    (qPochPoly y q m).eval T = qPoch (y * T) q m := by
  unfold qPochPoly qPoch
  rw [eval_prod]
  refine prod_congr rfl fun i _ => ?_
  simp only [eval_sub, eval_one, eval_mul, eval_C, eval_X]
  ring

lemma eval_Npoly (n : ℕ) (q T : ℝ) :
    (Npoly n q).eval T =
      qPoch q q n ^ 2 * qPoch ((q ^ n)⁻¹ * T) q n * qPoch (q ^ (n + 1) * T) q n * T ^ n := by
  simp only [Npoly, eval_mul, eval_C, eval_qPochPoly, eval_pow, eval_X]

/-- `(1/q; 1/q)_m² q^{m(m+1)} = (q; q)_m²`. -/
lemma qPoch_inv_sq (hq : q ≠ 0) (m : ℕ) :
    qPoch q⁻¹ q⁻¹ m ^ 2 * q ^ (m * (m + 1)) = qPoch q q m ^ 2 := by
  induction m with
  | zero => simp [qPoch]
  | succ m ih =>
    unfold qPoch at ih ⊢
    rw [prod_range_succ, prod_range_succ, mul_pow, mul_pow, ← ih]
    have key : (1 - q⁻¹ * q⁻¹ ^ m) * q ^ (m + 1) = -(1 - q * q ^ m) := by
      simp only [inv_pow]
      field_simp
      ring
    have key2 : (1 - q⁻¹ * q⁻¹ ^ m) ^ 2 * (q ^ (m + 1)) ^ 2 = (1 - q * q ^ m) ^ 2 := by
      rw [← mul_pow, key]
      ring
    have he : (m + 1) * (m + 1 + 1) = m * (m + 1) + 2 * (m + 1) := by ring
    rw [he, pow_add, pow_mul', ← key2]
    ring

/-- `(q^n T; 1/q)_n = (q^{n+1} V; q)_n` at `T = q^n V`. -/
lemma qPoch_inv_shift1 (hq : q ≠ 0) (n : ℕ) (V : ℝ) :
    qPoch ((q⁻¹ ^ n)⁻¹ * (q ^ n * V)) q⁻¹ n = qPoch (q ^ (n + 1) * V) q n := by
  unfold qPoch
  refine (prod_range_reflect _ n).symm.trans (prod_congr rfl fun i hi => ?_)
  have hi' : i + 1 ≤ n := mem_range.mp hi
  have he : n - 1 - i = n - (i + 1) := by omega
  rw [he, pow_sub₀ _ (inv_ne_zero hq) hi']
  simp only [inv_pow, inv_inv]
  field_simp
  ring

/-- `(q^{−n−1} T; 1/q)_n = (q^{−n} V; q)_n` at `T = q^n V`. -/
lemma qPoch_inv_shift2 (hq : q ≠ 0) (n : ℕ) (V : ℝ) :
    qPoch (q⁻¹ ^ (n + 1) * (q ^ n * V)) q⁻¹ n = qPoch ((q ^ n)⁻¹ * V) q n := by
  unfold qPoch
  refine (prod_range_reflect _ n).symm.trans (prod_congr rfl fun i hi => ?_)
  have hi' : i + 1 ≤ n := mem_range.mp hi
  have he : n - 1 - i = n - (i + 1) := by omega
  rw [he, pow_sub₀ _ (inv_ne_zero hq) hi']
  simp only [inv_pow, inv_inv]
  field_simp
  ring

/-- PROOF_T1 Lemma 2 for the numerator: `N(q^n V; 1/q) = q^{−n} N(V; q)`. -/
lemma eval_Npoly_inv (hq : q ≠ 0) (n : ℕ) (V : ℝ) :
    (Npoly n q⁻¹).eval (q ^ n * V) = (q ^ n)⁻¹ * (Npoly n q).eval V := by
  rw [eval_Npoly, eval_Npoly, qPoch_inv_shift1 hq, qPoch_inv_shift2 hq, ← qPoch_inv_sq hq n,
    show n * (n + 1) = n * n + n by ring, pow_add, mul_pow, ← pow_mul]
  have : q ^ n ≠ 0 := pow_ne_zero _ hq
  field_simp
  ring

lemma Npoly_comp_inv (hq : q ≠ 0) {n j : ℕ} (hj : j ≤ n) :
    (Npoly n q⁻¹).comp (Tsub q⁻¹ j) = C (q ^ n)⁻¹ * (Npoly n q).comp (Tsub q (n - j)) := by
  apply Polynomial.funext
  intro u
  have hT : (Tsub q⁻¹ j).eval u = q ^ n * (Tsub q (n - j)).eval u := by
    simp only [Tsub, eval_mul, eval_C, eval_sub, eval_one, eval_X]
    rw [pow_sub₀ q hq hj]
    simp only [inv_pow, inv_inv]
    have : q ^ n ≠ 0 := pow_ne_zero _ hq
    field_simp
  rw [eval_comp, eval_mul, eval_C, eval_comp, hT, eval_Npoly_inv hq]

lemma Dother_inv (hq : q ≠ 0) {n j : ℕ} (hj : j ≤ n) :
    Dother n q⁻¹ j = Dother n q (n - j) := by
  unfold Dother
  refine prod_nbij' (fun x => n - x) (fun x => n - x) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    simp only [mem_erase, mem_range] at ha ⊢
    omega
  · intro a ha
    simp only [mem_erase, mem_range] at ha ⊢
    omega
  · intro a ha
    simp only [mem_erase, mem_range] at ha
    omega
  · intro a ha
    simp only [mem_erase, mem_range] at ha
    omega
  · intro a ha
    simp only [mem_erase, mem_range] at ha
    have key : q⁻¹ ^ a * (q⁻¹ ^ j)⁻¹ = q ^ (n - a) * (q ^ (n - j))⁻¹ := by
      rw [pow_sub₀ q hq (by omega : a ≤ n), pow_sub₀ q hq hj]
      simp only [inv_pow, inv_inv]
      have : q ^ n ≠ 0 := pow_ne_zero _ hq
      have : q ^ a ≠ 0 := pow_ne_zero _ hq
      have : q ^ j ≠ 0 := pow_ne_zero _ hq
      field_simp
    simp only [Tsub, ← mul_assoc, ← C_mul, key]

/-- `Gser n q⁻¹ j = q^{−n} Gser n q (n − j)`. -/
lemma Gser_inv (hq : q ≠ 0) {n j : ℕ} (hj : j ≤ n) :
    Gser n q⁻¹ j = PowerSeries.C (q ^ n)⁻¹ * Gser n q (n - j) := by
  unfold Gser
  rw [Npoly_comp_inv hq hj, Dother_inv hq hj, Polynomial.coe_mul, Polynomial.coe_C, mul_assoc]

/-- Corollary of Lemma 2: `c_{s,j}(1/q) = q^{−n} c_{s,n−j}(q)`. -/
theorem cc_inv (hq : q ≠ 0) {n j : ℕ} (hj : j ≤ n) (s : ℕ) :
    cc n q⁻¹ s j = (q ^ n)⁻¹ * cc n q s (n - j) := by
  unfold cc
  rw [Gser_inv hq hj, PowerSeries.coeff_C_mul]

end QZeta3.Reciprocity
