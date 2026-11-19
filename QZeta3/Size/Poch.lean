import QZeta3.Statements

/-!
# Size: uniform bounds on `q`-Pochhammer symbols and on `R_n(q^m)`

PROOF_T1 §5 (Lemma 6), with `A = 4`, `r = 1`, `e = n`. Throughout `0 < |q| < 1` and `κ = |q|`.
The uniform constant is `K = κ/(1-κ)²`; for `a ≥ 1`, `e^{-K} ≤ |(q^a; q)_l| ≤ e^K`.
-/

open Finset Real

namespace QZeta3.Size

/-- The uniform constant `K = κ/(1-κ)²`, `κ = |q|`. -/
noncomputable def Kc (q : ℝ) : ℝ := |q| / (1 - |q|) ^ 2

lemma one_sub_bounds {κ t : ℝ} (hκ : κ < 1) (ht0 : 0 ≤ t) (htκ : t ≤ κ) :
    exp (-(t / (1 - κ))) ≤ 1 - t ∧ 1 + t ≤ exp (t / (1 - κ)) := by
  have h1 : 0 < 1 - κ := by linarith
  have h1t : 0 < 1 - t := by linarith
  constructor
  · have hle : t / (1 - t) ≤ t / (1 - κ) := div_le_div_of_nonneg_left ht0 h1 (by linarith)
    have h2 : 1 / (1 - t) ≤ exp (t / (1 - t)) := by
      have := add_one_le_exp (t / (1 - t))
      have e : t / (1 - t) + 1 = 1 / (1 - t) := by
        rw [div_add_one h1t.ne']; congr 1; ring
      linarith
    calc exp (-(t / (1 - κ))) ≤ exp (-(t / (1 - t))) := exp_le_exp.mpr (by linarith)
      _ = (exp (t / (1 - t)))⁻¹ := exp_neg _
      _ ≤ (1 / (1 - t))⁻¹ := inv_anti₀ (by positivity) h2
      _ = 1 - t := by simp
  · have : t ≤ t / (1 - κ) := le_div_self ht0 h1 (by linarith)
    calc 1 + t = t + 1 := by ring
      _ ≤ exp t := add_one_le_exp t
      _ ≤ exp (t / (1 - κ)) := exp_le_exp.mpr this

lemma abs_one_sub_pow_bounds {q : ℝ} (hq : |q| < 1) {j : ℕ} (hj : 1 ≤ j) :
    exp (-(|q| ^ j / (1 - |q|))) ≤ |1 - q ^ j| ∧ |1 - q ^ j| ≤ exp (|q| ^ j / (1 - |q|)) := by
  have h0 : 0 ≤ |q| ^ j := by positivity
  have hle : |q| ^ j ≤ |q| := pow_le_of_le_one (abs_nonneg q) hq.le (by omega)
  obtain ⟨h1, h2⟩ := one_sub_bounds hq h0 hle
  have ha : |q ^ j| = |q| ^ j := abs_pow q j
  constructor
  · calc _ ≤ 1 - |q| ^ j := h1
      _ = |1| - |q ^ j| := by rw [ha, abs_one]
      _ ≤ |1 - q ^ j| := abs_sub_abs_le_abs_sub _ _
  · calc |1 - q ^ j| ≤ |1| + |q ^ j| := abs_sub _ _
      _ = 1 + |q| ^ j := by rw [ha, abs_one]
      _ ≤ _ := h2

lemma geom_bound {κ : ℝ} (h0 : 0 ≤ κ) (h1 : κ < 1) (a l : ℕ) (ha : 1 ≤ a) :
    ∑ i ∈ range l, κ ^ (a + i) ≤ κ / (1 - κ) := by
  have e : ∑ i ∈ range l, κ ^ (a + i) = ∑ i ∈ Ico a (a + l), κ ^ i := by
    rw [sum_Ico_eq_sum_range]; simp
  rw [e]
  calc _ ≤ κ ^ a / (1 - κ) := geom_sum_Ico_le_of_lt_one h0 h1
    _ ≤ κ / (1 - κ) := div_le_div_of_nonneg_right
        (pow_le_of_le_one h0 h1.le (by omega)) (by linarith)

/-- For `a ≥ 1`: `e^{-K} ≤ |(q^a; q)_l| ≤ e^K`, uniformly in `a` and `l`. -/
lemma poch_bounds {q : ℝ} (hq : |q| < 1) {a : ℕ} (ha : 1 ≤ a) (l : ℕ) :
    exp (-Kc q) ≤ |qPoch (q ^ a) q l| ∧ |qPoch (q ^ a) q l| ≤ exp (Kc q) := by
  have h1 : 0 < 1 - |q| := by linarith
  have hsum : ∑ i ∈ range l, |q| ^ (a + i) / (1 - |q|) ≤ Kc q := by
    rw [← sum_div, Kc, sq, ← div_div]
    exact div_le_div_of_nonneg_right (geom_bound (abs_nonneg q) hq a l ha) h1.le
  have habs : |qPoch (q ^ a) q l| = ∏ i ∈ range l, |1 - q ^ (a + i)| := by
    rw [qPoch, abs_prod]; simp [pow_add]
  rw [habs]
  constructor
  · calc exp (-Kc q) ≤ exp (-(∑ i ∈ range l, |q| ^ (a + i) / (1 - |q|))) :=
          exp_le_exp.mpr (by linarith)
      _ = ∏ i ∈ range l, exp (-(|q| ^ (a + i) / (1 - |q|))) := by
          rw [← sum_neg_distrib, exp_sum]
      _ ≤ _ := prod_le_prod₀ (fun i _ => (exp_pos _).le)
          (fun i _ => (abs_one_sub_pow_bounds hq (by omega)).1)
  · calc _ ≤ ∏ i ∈ range l, exp (|q| ^ (a + i) / (1 - |q|)) :=
          prod_le_prod₀ (fun i _ => abs_nonneg _)
            (fun i _ => (abs_one_sub_pow_bounds hq (by omega)).2)
      _ = exp (∑ i ∈ range l, |q| ^ (a + i) / (1 - |q|)) := (exp_sum _ _).symm
      _ ≤ exp (Kc q) := exp_le_exp.mpr hsum

/-- `R_n(q^m) = 0` for `1 ≤ m ≤ n`. -/
lemma Rfun_pow_eq_zero {q : ℝ} (hq0 : q ≠ 0) {n m : ℕ} (hm1 : 1 ≤ m) (hmn : m ≤ n) :
    Rfun n q (q ^ m) = 0 := by
  have hz : qPoch ((q ^ n)⁻¹ * q ^ m) q n = 0 := by
    rw [qPoch]
    apply prod_eq_zero (i := n - m) (by simp; omega)
    rw [mul_assoc, ← pow_add, show m + (n - m) = n by omega,
      inv_mul_cancel₀ (pow_ne_zero _ hq0), sub_self]
  rw [Rfun, hz]; simp

lemma exp_combo (K : ℝ) : exp K ^ 2 * exp K * exp K / exp (-K) ^ 4 = exp (8 * K) := by
  rw [← exp_nat_mul, ← exp_nat_mul, ← exp_add, ← exp_add, ← exp_sub]; congr 1; push_cast; ring

lemma exp_combo' (K : ℝ) : exp (-K) ^ 2 * exp (-K) * exp (-K) / exp K ^ 4 = exp (-(8 * K)) := by
  have := exp_combo (-K); rw [neg_neg] at this; rw [this]; congr 1; ring

/-- For `m ≥ n + 1`: `e^{-8K} κ^{mn} ≤ |R_n(q^m)| ≤ e^{8K} κ^{mn}`. -/
lemma Rfun_pow_bounds {q : ℝ} (hq0 : q ≠ 0) (hq : |q| < 1) {n m : ℕ} (hm : n + 1 ≤ m) :
    exp (-(8 * Kc q)) * |q| ^ (m * n) ≤ |Rfun n q (q ^ m)| ∧
      |Rfun n q (q ^ m)| ≤ exp (8 * Kc q) * |q| ^ (m * n) := by
  have e1 : (q ^ n)⁻¹ * q ^ m = q ^ (m - n) := by
    rw [pow_sub₀ q hq0 (by omega : n ≤ m), mul_comm]
  have e2 : q ^ (n + 1) * q ^ m = q ^ (n + 1 + m) := (pow_add _ _ _).symm
  have hR : |Rfun n q (q ^ m)| = |qPoch q q n| ^ 2 * |qPoch (q ^ (m - n)) q n| *
      |qPoch (q ^ (n + 1 + m)) q n| * |q| ^ (m * n) / |qPoch (q ^ m) q (n + 1)| ^ 4 := by
    rw [Rfun, e1, e2, ← pow_mul]; simp [abs_div, abs_mul, abs_pow]
  have hA := poch_bounds hq (le_refl 1) n
  simp only [pow_one] at hA
  have hB := poch_bounds hq (by omega : 1 ≤ m - n) n
  have hC := poch_bounds hq (by omega : 1 ≤ n + 1 + m) n
  have hD := poch_bounds hq (by omega : 1 ≤ m) (n + 1)
  have hDpos : 0 < |qPoch (q ^ m) q (n + 1)| := lt_of_lt_of_le (exp_pos _) hD.1
  have hx : 0 ≤ |q| ^ (m * n) := by positivity
  rw [hR]
  constructor
  · calc exp (-(8 * Kc q)) * |q| ^ (m * n)
        = exp (-Kc q) ^ 2 * exp (-Kc q) * exp (-Kc q) * |q| ^ (m * n) / exp (Kc q) ^ 4 := by
          rw [← exp_combo']; ring
      _ ≤ _ := by gcongr <;> first | exact hA.1 | exact hB.1 | exact hC.1 | exact hD.2
  · calc _ ≤ exp (Kc q) ^ 2 * exp (Kc q) * exp (Kc q) * |q| ^ (m * n) / exp (-Kc q) ^ 4 := by
          gcongr <;> first | exact hA.2 | exact hB.2 | exact hC.2 | exact hD.1
      _ = exp (8 * Kc q) * |q| ^ (m * n) := by rw [← exp_combo]; ring

end QZeta3.Size
