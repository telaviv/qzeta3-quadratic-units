import QZeta3.Statements

/-!
# Analytic pieces for Lemma 4 (expansion), A = 4

For real `0 < |q| < 1` and `y = q^{m+1}` (`m : ℕ`):
* `fS s y = (1 − y)^{−s} − 1`, `gS s y = (1 − y^{−1})^{−s}` (the two sides of PROOF_T1 §3);
* `lam y = y/(1 − y)` (Lambert term), `zet y = y(1 + y)/(1 − y)³`;
* termwise `fS s y − gS s y = 2 lam y + aS s · zet y` with `aS = 0, 0, 1, 2` for `s = 1..4`;
* `Σ_m zet(q^{m+1}) = ζ_q(3)` (swap of an absolutely convergent double series);
* summability of `lam`, `gS s`, `fS s` along `q^{m+1}`.
-/

open Finset

namespace QZeta3.Expand

/-- `(1 − y)^{−s} − 1`. -/
noncomputable def fS (s : ℕ) (y : ℝ) : ℝ := ((1 - y) ^ s)⁻¹ - 1

/-- `(1 − y^{−1})^{−s}`. -/
noncomputable def gS (s : ℕ) (y : ℝ) : ℝ := ((1 - y⁻¹) ^ s)⁻¹

/-- Lambert term `y/(1 − y)`. -/
noncomputable def lam (y : ℝ) : ℝ := y / (1 - y)

/-- `y(1 + y)/(1 − y)³ = Σ_{i ≥ 1} i² yⁱ`. -/
noncomputable def zet (y : ℝ) : ℝ := y * (1 + y) / (1 - y) ^ 3

/-- The weight of `zet` in `fS s − gS s`: `0, 0, 1, 2` for `s = 1, 2, 3, 4`. -/
noncomputable def aS (s : ℕ) : ℝ := if s = 3 then 1 else if s = 4 then 2 else 0

lemma sum_Icc14 (φ : ℕ → ℝ) : ∑ s ∈ Icc 1 4, φ s = φ 1 + φ 2 + φ 3 + φ 4 := by
  rw [show (Icc 1 4 : Finset ℕ) = {1, 2, 3, 4} by decide]
  simp [sum_insert]
  ring

lemma sum_Icc_one (N : ℕ) (φ : ℕ → ℝ) : ∑ m ∈ Icc 1 N, φ m = ∑ i ∈ range N, φ (i + 1) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  simp [add_comm]

/-- The termwise identity of PROOF_T1 §3 (brief: `(1 − (−y)^s)/(1 − y)^s − 1`). -/
lemma fS_sub_gS {s : ℕ} (hs : s ∈ Icc 1 4) {y : ℝ} (hy0 : y ≠ 0) (hy1 : y ≠ 1) :
    fS s y - gS s y = 2 * lam y + aS s * zet y := by
  have h1 : 1 - y ≠ 0 := sub_ne_zero.mpr (Ne.symm hy1)
  have h2 : y - 1 ≠ 0 := sub_ne_zero.mpr hy1
  have h3 : 1 - y⁻¹ = (y - 1) / y := by field_simp
  rw [Finset.mem_Icc] at hs
  obtain ⟨hs1, hs4⟩ := hs
  interval_cases s <;>
  · simp only [fS, gS, lam, zet, aS, h3]
    norm_num
    field_simp
    ring

/-! ### Elementary bounds -/

section Bounds

set_option linter.unusedSectionVars false

variable {q : ℝ} (hq0 : q ≠ 0) (hq : |q| < 1)
include hq0 hq

lemma abs_pow_succ_le (m : ℕ) : |q ^ (m + 1)| ≤ |q| ^ m := by
  rw [abs_pow]
  exact pow_le_pow_of_le_one (abs_nonneg q) hq.le (Nat.le_succ m)

lemma abs_pow_succ_lt (m : ℕ) : |q ^ (m + 1)| < 1 := by
  rw [abs_pow]
  exact pow_lt_one₀ (abs_nonneg q) hq (Nat.succ_ne_zero m)

lemma pow_succ_ne_one (m : ℕ) : q ^ (m + 1) ≠ 1 := by
  intro h
  have := abs_pow_succ_lt hq0 hq m
  rw [h, abs_one] at this
  exact lt_irrefl _ this

lemma one_sub_le_abs (m : ℕ) : 1 - |q| ≤ |1 - q ^ (m + 1)| := by
  have h1 : |q ^ (m + 1)| ≤ |q| := by
    rw [abs_pow]
    exact pow_le_of_le_one (abs_nonneg q) hq.le (Nat.succ_ne_zero m)
  have h2 := abs_sub_abs_le_abs_sub (1 : ℝ) (q ^ (m + 1))
  rw [abs_one] at h2
  linarith

lemma summable_lam : Summable fun m : ℕ => lam (q ^ (m + 1)) := by
  have hδ : 0 < 1 - |q| := by linarith
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one (abs_nonneg q) hq).mul_right (1 - |q|)⁻¹) fun m => ?_
  rw [Real.norm_eq_abs, lam, abs_div, ← div_eq_mul_inv]
  gcongr
  · exact abs_pow_succ_le hq0 hq m
  · exact one_sub_le_abs hq0 hq m

lemma summable_gS {s : ℕ} (hs : 1 ≤ s) : Summable fun m : ℕ => gS s (q ^ (m + 1)) := by
  have hδ : 0 < 1 - |q| := by linarith
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one (abs_nonneg q) hq).mul_right
      (((1 - |q|)⁻¹) ^ t * (1 - |q|)⁻¹)) fun m => ?_
  set y := q ^ (m + 1) with hy
  have hy0 : y ≠ 0 := pow_ne_zero _ hq0
  have h2 : y - 1 ≠ 0 := sub_ne_zero.mpr (pow_succ_ne_one hq0 hq m)
  have hg : gS (t + 1) y = (y / (y - 1)) ^ (t + 1) := by
    rw [gS, show 1 - y⁻¹ = (y - 1) / y by field_simp, div_pow, div_pow, inv_div]
  have hA : |y - 1| = |1 - y| := abs_sub_comm _ _
  have hB : 1 - |q| ≤ |1 - y| := one_sub_le_abs hq0 hq m
  have hC : |y| ≤ |q| ^ m := abs_pow_succ_le hq0 hq m
  have hD : |y| ≤ 1 := (abs_pow_succ_lt hq0 hq m).le
  have hx0 : 0 ≤ |y| / |1 - y| := by positivity
  have hx1 : |y| / |1 - y| ≤ (1 - |q|)⁻¹ := by
    rw [inv_eq_one_div]; gcongr
  have hx2 : |y| / |1 - y| ≤ |q| ^ m * (1 - |q|)⁻¹ := by
    rw [← div_eq_mul_inv]; gcongr
  rw [Real.norm_eq_abs, hg, abs_pow, abs_div, hA, pow_succ]
  calc (|y| / |1 - y|) ^ t * (|y| / |1 - y|)
      ≤ ((1 - |q|)⁻¹) ^ t * (|q| ^ m * (1 - |q|)⁻¹) := by gcongr
    _ = |q| ^ m * (((1 - |q|)⁻¹) ^ t * (1 - |q|)⁻¹) := by ring

end Bounds

/-! ### `Σ i² rⁱ` and the double series -/

lemma hasSum_sq_geom {r : ℝ} (hr : |r| < 1) :
    HasSum (fun i : ℕ => ((i : ℝ) + 1) ^ 2 * r ^ (i + 1)) (r * (1 + r) / (1 - r) ^ 3) := by
  have hr' : ‖r‖ < 1 := by rwa [Real.norm_eq_abs]
  have hsum : Summable fun i : ℕ => (i : ℝ) ^ 2 * r ^ i :=
    summable_pow_mul_geometric_of_norm_lt_one 2 hr'
  set S := ∑' i : ℕ, (i : ℝ) ^ 2 * r ^ i with hS
  have h1 : HasSum (fun i : ℕ => ((i : ℝ) + 1) ^ 2 * r ^ (i + 1)) S := by
    have := (hasSum_nat_add_iff' (f := fun i : ℕ => (i : ℝ) ^ 2 * r ^ i) 1).mpr hsum.hasSum
    simpa using this
  have h2 : HasSum (fun i : ℕ => ((i : ℝ) + 1) ^ 2 * r ^ (i + 1))
      (r * S + r * (2 * (r / (1 - r) ^ 2) + (1 - r)⁻¹)) := by
    have := (hsum.hasSum.mul_left r).add
      (((hasSum_coe_mul_geometric_of_norm_lt_one hr').mul_left 2).add
        (hasSum_geometric_of_abs_lt_one hr) |>.mul_left r)
    convert this using 1
    funext i
    ring
  have hr1 : 1 - r ≠ 0 := by
    intro h
    have : r = 1 := by linarith
    rw [this, abs_one] at hr
    exact lt_irrefl _ hr
  have hS' : S = r * (1 + r) / (1 - r) ^ 3 := by
    have he := h1.unique h2
    field_simp
    field_simp at he
    linear_combination he
  rw [← hS']
  exact h1

lemma hasSum_zet {q : ℝ} (hq0 : q ≠ 0) (hq : |q| < 1) :
    HasSum (fun m : ℕ => zet (q ^ (m + 1))) (zetaq3 q) := by
  set h : ℕ × ℕ → ℝ := fun p => ((p.2 : ℝ) + 1) ^ 2 * q ^ ((p.1 + 1) * (p.2 + 1)) with hh
  have hqa : |(|q|)| < 1 := by rwa [abs_abs]
  have hsumm : Summable h := by
    refine Summable.of_norm_bounded
      ((summable_geometric_of_lt_one (abs_nonneg q) hq).mul_of_nonneg
        (hasSum_sq_geom hqa).summable (fun _ => by positivity) (fun _ => by positivity))
      fun p => ?_
    rw [Real.norm_eq_abs, hh, abs_mul, abs_pow, abs_pow]
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((p.2 : ℝ) + 1))]
    calc ((p.2 : ℝ) + 1) ^ 2 * |q| ^ ((p.1 + 1) * (p.2 + 1))
        ≤ ((p.2 : ℝ) + 1) ^ 2 * |q| ^ (p.1 + (p.2 + 1)) := by
          refine mul_le_mul_of_nonneg_left
            (pow_le_pow_of_le_one (abs_nonneg q) hq.le ?_) (by positivity)
          nlinarith [Nat.zero_le (p.1 * p.2)]
      _ = |q| ^ p.1 * (((p.2 : ℝ) + 1) ^ 2 * |q| ^ (p.2 + 1)) := by rw [pow_add]; ring
  set T := ∑' p, h p
  -- fibre over `m`: `Σ_i (i+1)² (q^{m+1})^{i+1} = zet (q^{m+1})`
  have hA : HasSum (fun m : ℕ => zet (q ^ (m + 1))) T := by
    refine hsumm.hasSum.prod_fiberwise fun m => ?_
    have := hasSum_sq_geom (abs_pow_succ_lt hq0 hq m)
    simp only [hh, zet]
    convert this using 2 with i
    rw [pow_mul]
  -- fibre over `i`: `Σ_m (i+1)² (q^{i+1})^{m+1} = (i+1)² q^{i+1}/(1 − q^{i+1})`
  have hB : HasSum (fun i : ℕ => ((i : ℝ) + 1) ^ 2 * (q ^ (i + 1) / (1 - q ^ (i + 1)))) T := by
    have hsw : HasSum (h ∘ (Equiv.prodComm ℕ ℕ)) T :=
      (Equiv.prodComm ℕ ℕ).hasSum_iff.mpr hsumm.hasSum
    refine hsw.prod_fiberwise fun i => ?_
    have hg := ((hasSum_geometric_of_abs_lt_one (abs_pow_succ_lt hq0 hq i)).mul_left
      (q ^ (i + 1))).mul_left (((i : ℝ) + 1) ^ 2)
    simp only [Function.comp, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap, hh]
    convert hg using 2 with m
    · rw [mul_comm (m + 1) (i + 1), pow_mul, pow_succ]; ring
    · rw [div_eq_mul_inv]
  have hZ : HasSum (fun m : ℕ => (m : ℝ) ^ 2 * q ^ m / (1 - q ^ m)) T := by
    refine (hasSum_nat_add_iff' (f := fun m : ℕ => (m : ℝ) ^ 2 * q ^ m / (1 - q ^ m)) 1).mp ?_
    simpa [mul_div_assoc] using hB
  rw [zetaq3, hZ.tsum_eq]
  exact hA

lemma summable_zet {q : ℝ} (hq0 : q ≠ 0) (hq : |q| < 1) :
    Summable fun m : ℕ => zet (q ^ (m + 1)) := (hasSum_zet hq0 hq).summable

lemma summable_fS {q : ℝ} (hq0 : q ≠ 0) (hq : |q| < 1) {s : ℕ} (hs : s ∈ Icc 1 4) :
    Summable fun m : ℕ => fS s (q ^ (m + 1)) := by
  have h := (((summable_lam hq0 hq).mul_left 2).add ((summable_zet hq0 hq).mul_left (aS s))).add
    (summable_gS hq0 hq (Finset.mem_Icc.mp hs).1)
  convert h using 1
  funext m
  rw [← fS_sub_gS hs (pow_ne_zero _ hq0) (pow_succ_ne_one hq0 hq m)]
  ring

end QZeta3.Expand
