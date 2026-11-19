import QZeta3.Main
import QZeta3.Corollary

/-!
# From the ingredients to the final statements

`Ingredients` bundles the six frozen ingredients; `Final.lean` discharges it with the workers'
theorems. Here, assuming it, we derive the √d form of T1, the Lucas-sequence corollary and the
Fibonacci case, and prove (unconditionally) that the series defining `zetaq3` converges.
-/

open Polynomial Finset

namespace QZeta3

/-- The six frozen ingredients. -/
def Ingredients : Prop :=
  PFIdentity ∧ (PFIdentity → Expansion) ∧ (PFIdentity → Recip) ∧ Integrality ∧ SizeBound ∧ CostBound

theorem irrational_sub_inv_mul_zetaq3_ing (H : Ingredients) {q : ℝ} {s : ℤ} (hq0 : q ≠ 0)
    (hq1 : |q| < 1) (hs : q + q⁻¹ = s) : Irrational ((q - q⁻¹) * zetaq3 q) :=
  irrational_sub_inv_mul_zetaq3_of H.1 H.2.1 H.2.2.1 H.2.2.2.1 H.2.2.2.2.1 H.2.2.2.2.2 hq0 hq1 hs

theorem irrational_sqrt_mul_zetaq3_ing (H : Ingredients) {q : ℝ} {s : ℤ} (hq0 : q ≠ 0)
    (hq1 : |q| < 1) (hs : q + q⁻¹ = s) {d : ℕ} (hd : 0 < d)
    (hsq : IsSquare ((d : ℤ) * (s ^ 2 - 4))) : Irrational (Real.sqrt d * zetaq3 q) := by
  have hmain := irrational_sub_inv_mul_zetaq3_ing H hq0 hq1 hs
  obtain ⟨m, hm⟩ := hsq
  set θ := q - q⁻¹ with hθ
  have hθ2 : θ ^ 2 = (s : ℝ) ^ 2 - 4 := by
    have : θ ^ 2 = (q + q⁻¹) ^ 2 - 4 * (q * q⁻¹) := by rw [hθ]; ring
    rw [this, mul_inv_cancel₀ hq0, hs]; ring
  have hθ0 : θ ≠ 0 := by
    intro h
    have h1 : q * q = 1 := by
      have : q = q⁻¹ := sub_eq_zero.mp h
      calc q * q = q * q⁻¹ := by rw [← this]
        _ = 1 := mul_inv_cancel₀ hq0
    have : |q| * |q| = 1 := by rw [← abs_mul, h1, abs_one]
    nlinarith [abs_nonneg q]
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  -- (√d θ)² = d (s² − 4) = m², so √d θ = ±m
  have hsq' : (Real.sqrt d * θ) ^ 2 = (m : ℝ) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hd0, hθ2]
    have : ((d : ℤ) * (s ^ 2 - 4) : ℤ) = m * m := hm
    have hR : (((d : ℤ) * (s ^ 2 - 4) : ℤ) : ℝ) = ((m * m : ℤ) : ℝ) := by rw [this]
    push_cast at hR; rw [hR]; ring
  have hm' : ∃ m' : ℤ, Real.sqrt d * θ = m' := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq' with h | h
    · exact ⟨m, h⟩
    · exact ⟨-m, by rw [h]; push_cast; ring⟩
  obtain ⟨m', hm'⟩ := hm'
  have hsqrt0 : Real.sqrt d ≠ 0 := by
    rw [Real.sqrt_ne_zero']; exact_mod_cast hd
  have hm'0 : (m' : ℝ) ≠ 0 := by rw [← hm']; exact mul_ne_zero hsqrt0 hθ0
  have hS0 : (s : ℝ) ^ 2 - 4 ≠ 0 := by rw [← hθ2]; exact pow_ne_zero 2 hθ0
  have hq : ((m' : ℚ) / ((s : ℚ) ^ 2 - 4)) ≠ 0 := by
    have hm'q : (m' : ℚ) ≠ 0 := by exact_mod_cast (fun h => hm'0 (by exact_mod_cast h))
    have hSq : ((s : ℚ) ^ 2 - 4) ≠ 0 := by
      intro h; apply hS0; have := congrArg (fun x : ℚ => (x : ℝ)) h; push_cast at this; exact this
    exact div_ne_zero hm'q hSq
  have key : Real.sqrt d * zetaq3 q = (((m' : ℚ) / ((s : ℚ) ^ 2 - 4) : ℚ) : ℝ) * (θ * zetaq3 q) := by
    push_cast
    rw [← hθ2]
    have : Real.sqrt d = m' / θ := by field_simp; linarith
    rw [this]; field_simp
  rw [key]
  exact Irrational.ratCast_mul hmain hq

theorem lucas_sum_eq {a : ℕ} {E : ℤ} (h : Adm a E) :
    ∑' m : ℕ, (m : ℝ) ^ 2 * ((lucasU a E (m + 1) : ℝ) / lucasU a E m - epsU a E) =
      Real.sqrt ((a : ℝ) ^ 2 + 4 * E) * zetaq3 (qU a E) := by
  rw [show (fun m : ℕ => (m : ℝ) ^ 2 * ((lucasU a E (m + 1) : ℝ) / lucasU a E m - epsU a E)) =
      fun m : ℕ => Real.sqrt ((a : ℝ) ^ 2 + 4 * E) * ((m : ℝ) ^ 2 * qU a E ^ m / (1 - qU a E ^ m))
      from funext (term_eq h)]
  rw [tsum_mul_left]; rfl

theorem irrational_lucas_sum_ing (H : Ingredients) {a : ℕ} {E : ℤ}
    (h : (E = 1 ∧ 1 ≤ a) ∨ (E = -1 ∧ 3 ≤ a)) :
    Irrational (∑' m : ℕ, (m : ℝ) ^ 2 * ((lucasU a E (m + 1) : ℝ) / lucasU a E m - epsU a E)) := by
  have hA : Adm a E := h
  rw [lucas_sum_eq hA]
  have hpos := discr_pos hA
  set d : ℕ := (discr a E).toNat with hd
  have hdZ : (d : ℤ) = discr a E := Int.toNat_of_nonneg hpos.le
  have hdR : (d : ℝ) = (a : ℝ) ^ 2 + 4 * E := by
    rw [← discr_cast, ← hdZ]; rfl
  rw [← hdR]
  refine irrational_sqrt_mul_zetaq3_ing H (qU_ne_zero hA) (abs_qU_lt_one hA) (qU_add_inv hA)
    (by omega) ?_
  rw [hdZ]; exact discr_mul_sq hA

theorem lucasU_one_one (m : ℕ) : lucasU 1 1 m = Nat.fib m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    match m, ih with
    | 0, _ => simp [lucasU]
    | 1, _ => simp [lucasU]
    | (m + 2), ih =>
      simp only [lucasU, Nat.cast_one, one_mul]
      rw [ih (m + 1) (by omega), ih m (by omega), Nat.fib_add_two]; push_cast; ring

theorem epsU_one_one : epsU 1 1 = Real.goldenRatio := by
  unfold epsU Real.goldenRatio; norm_num

theorem irrational_fib_sum_ing (H : Ingredients) :
    Irrational (∑' m : ℕ, (m : ℝ) ^ 2 * ((Nat.fib (m + 1) : ℝ) / Nat.fib m - Real.goldenRatio)) := by
  have := irrational_lucas_sum_ing H (a := 1) (E := 1) (Or.inl ⟨rfl, le_refl 1⟩)
  simpa only [lucasU_one_one, epsU_one_one, Int.cast_natCast] using this

/-- The series defining `ζ_q(3)` converges for `|q| < 1`. -/
theorem summable_zetaq3 {q : ℝ} (hq1 : |q| < 1) :
    Summable (fun m : ℕ => (m : ℝ) ^ 2 * q ^ m / (1 - q ^ m)) := by
  have hκ0 : 0 ≤ |q| := abs_nonneg q
  have hpos : 0 < 1 - |q| := by linarith
  have hg : Summable (fun m : ℕ => (1 - |q|)⁻¹ * ((m : ℝ) ^ 2 * |q| ^ m)) := by
    have := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 2 (r := |q|)
      (by rw [Real.norm_eq_abs, abs_abs]; exact hq1)
    exact this.mul_left _
  refine Summable.of_norm_bounded hg (fun m => ?_)
  rw [Real.norm_eq_abs]
  rcases Nat.eq_zero_or_pos m with h0 | hm
  · subst h0; norm_num
  have h1 : 1 - |q| ≤ |1 - q ^ m| := by
    have h2 : |q ^ m| ≤ |q| := by
      rw [abs_pow]; exact pow_le_of_le_one hκ0 hq1.le hm.ne'
    have h3 := abs_sub_abs_le_abs_sub (1 : ℝ) (q ^ m)
    rw [abs_one] at h3; linarith
  have hden : 0 < |1 - q ^ m| := lt_of_lt_of_le hpos h1
  rw [abs_div, abs_mul, abs_pow, abs_pow, Nat.abs_cast, div_le_iff₀ hden]
  have e : (m : ℝ) ^ 2 * |q| ^ m = (1 - |q|)⁻¹ * ((m : ℝ) ^ 2 * |q| ^ m) * (1 - |q|) := by
    field_simp
  have hA : 0 ≤ (1 - |q|)⁻¹ * ((m : ℝ) ^ 2 * |q| ^ m) := by positivity
  calc (m : ℝ) ^ 2 * |q| ^ m = (1 - |q|)⁻¹ * ((m : ℝ) ^ 2 * |q| ^ m) * (1 - |q|) := e
    _ ≤ (1 - |q|)⁻¹ * ((m : ℝ) ^ 2 * |q| ^ m) * |1 - q ^ m| :=
      mul_le_mul_of_nonneg_left h1 hA

/-- The Lucas series converges (so its `tsum` is not a junk value). -/
theorem summable_lucas {a : ℕ} {E : ℤ} (h : (E = 1 ∧ 1 ≤ a) ∨ (E = -1 ∧ 3 ≤ a)) :
    Summable (fun m : ℕ => (m : ℝ) ^ 2 * ((lucasU a E (m + 1) : ℝ) / lucasU a E m - epsU a E)) := by
  rw [show (fun m : ℕ => (m : ℝ) ^ 2 * ((lucasU a E (m + 1) : ℝ) / lucasU a E m - epsU a E)) =
      fun m : ℕ => Real.sqrt ((a : ℝ) ^ 2 + 4 * E) * ((m : ℝ) ^ 2 * qU a E ^ m / (1 - qU a E ^ m))
      from funext (term_eq h)]
  exact (summable_zetaq3 (abs_qU_lt_one h)).mul_left _

end QZeta3
