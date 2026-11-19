-- Adapted from lean_lucasu LucasU/Cost/Cyclo.lean.
-- Generalised from lean_fibzeta FibZeta/Cost/Cyclo.lean (ε = ±1, general t).
/-
Adapted from uplift-universal-inc/qzeta_3-irrationality, lean/QZeta3/CyclotomicBounds.lean (Apache-2.0, Lean
formalisation by F. Solomon Admasu). Changes: the integer point `p` is replaced by the pair `q`, `1/q` (norm of
`Φ_ℓ(q)` in a real quadratic field when `q` is a unit of norm `+1`), with the error bound `|q|ⁿ/(1 − |q|)` for
`log|1 − qⁿ|`, valid for every `0 < |q| < 1`.
-/
import QZeta3.Statements

/-!
# Lemma 7, per cyclotomic factor: size of `Φ_ℓ(q) Φ_ℓ(1/q)`

For real `q` with `0 < |q| < 1` and every `ℓ ≥ 1`:
`|Φ_ℓ(q) Φ_ℓ(1/q)| ≤ exp(2/(1 − |q|)²) · |q|^{−φ(ℓ)}` (`norm_cyc_le`).

Proof: `∑_{a ∣ n} log|Φ_a(x)| = log|xⁿ − 1|`; at `x = q` and `x = 1/q` the sum of the two minus `n log|q|⁻¹` is
`G(n) = 2 log|1 − qⁿ|`, and `|G(n)| ≤ 2|q|ⁿ/(1 − |q|)`; Möbius inversion gives
`|F(ℓ)| ≤ ∑_{a ∣ ℓ} 2|q|ᵃ/(1 − |q|) ≤ 2/(1 − |q|)²`.
-/

open Polynomial Finset
open scoped ArithmeticFunction.Moebius

namespace QZeta3.Cost

variable {q : ℝ}

theorem pow_ne_one_of_abs_ne_one {τ : ℝ} (h : |τ| ≠ 1) : ∀ m : ℕ, 0 < m → τ ^ m ≠ 1 := by
  intro m hm hτ
  apply h
  have : |τ| ^ m = 1 := by rw [← abs_pow, hτ, abs_one]
  exact (pow_eq_one_iff_of_nonneg (abs_nonneg τ) hm.ne').mp this

theorem abs_log_one_sub_le {κ v : ℝ} (hκ : κ < 1) (hv : |v| ≤ κ) :
    |Real.log (|1 - v|)| ≤ |v| / (1 - κ) := by
  have hv1 : v ≤ κ := le_trans (le_abs_self v) hv
  have h1 : 0 < 1 - v := by linarith
  have hk : 0 < 1 - κ := by linarith
  rw [abs_of_pos h1]
  have habs := abs_nonneg v
  have hle := le_abs_self v
  have hge := neg_abs_le v
  have hvk : |v| ≤ |v| / (1 - κ) := by
    rw [le_div_iff₀ hk]
    nlinarith [mul_nonneg habs (habs.trans hv)]
  refine abs_le.mpr ⟨?_, ?_⟩
  · have hlow := Real.one_sub_inv_le_log_of_pos h1
    have e1 : (1 - v)⁻¹ - 1 = v / (1 - v) := by field_simp; ring
    have e2 : v / (1 - v) ≤ |v| / (1 - κ) := by
      rw [div_le_div_iff₀ h1 hk]
      rcases le_or_gt 0 v with hv0 | hv0
      · rw [abs_of_nonneg hv0]; nlinarith
      · rw [abs_of_neg hv0]; nlinarith
    linarith
  · have := Real.log_le_sub_one_of_pos h1
    linarith

theorem aeval_cyc (ℓ : ℕ) (x : ℝ) : aeval x (cyclotomic ℓ ℤ) = (cyclotomic ℓ ℝ).eval x := by
  rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]

theorem cyc_eval_ne_zero {x : ℝ} (hx : ∀ m : ℕ, 0 < m → x ^ m ≠ 1) {a : ℕ} (ha : 0 < a) :
    (cyclotomic a ℝ).eval x ≠ 0 := by
  intro h
  have : NeZero a := ⟨ha.ne'⟩
  have hroot : (cyclotomic a ℝ).IsRoot x := h
  rw [isRoot_cyclotomic_iff] at hroot
  exact hx a ha hroot.pow_eq_one

theorem sum_log_cyc {x : ℝ} (hx : ∀ m : ℕ, 0 < m → x ^ m ≠ 1) {n : ℕ} (hn : 0 < n) :
    ∑ a ∈ n.divisors, Real.log |(cyclotomic a ℝ).eval x| = Real.log |x ^ n - 1| := by
  rw [← Real.log_prod (fun a ha => abs_ne_zero.mpr
    (cyc_eval_ne_zero hx (Nat.pos_of_mem_divisors ha))), ← Finset.abs_prod, ← eval_prod,
    prod_cyclotomic_eq_X_pow_sub_one hn]
  simp

theorem not_root (hq1 : |q| < 1) : ∀ m : ℕ, 0 < m → q ^ m ≠ 1 :=
  pow_ne_one_of_abs_ne_one hq1.ne

theorem not_root_inv (hq0 : q ≠ 0) (hq1 : |q| < 1) : ∀ m : ℕ, 0 < m → q⁻¹ ^ m ≠ 1 := by
  apply pow_ne_one_of_abs_ne_one
  rw [abs_inv]
  exact (one_lt_inv_iff₀.mpr ⟨abs_pos.mpr hq0, hq1⟩).ne'

/-- The cyclotomic error `F(a) = log|Φ_a(q)| + log|Φ_a(1/q)| − φ(a) log|q|⁻¹`. -/
noncomputable def cycErr (q : ℝ) (a : ℕ) : ℝ :=
  Real.log |(cyclotomic a ℝ).eval q| + Real.log |(cyclotomic a ℝ).eval q⁻¹| -
    (Nat.totient a : ℝ) * Real.log |q|⁻¹

/-- `G(n) = 2 log|1 − qⁿ|`. -/
noncomputable def cycG (q : ℝ) (n : ℕ) : ℝ := 2 * Real.log |1 - q ^ n|

theorem sum_cycErr (hq0 : q ≠ 0) (hq1 : |q| < 1) {n : ℕ} (hn : 0 < n) :
    ∑ a ∈ n.divisors, cycErr q a = cycG q n := by
  unfold cycErr cycG
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, sum_log_cyc (not_root hq1) hn,
    sum_log_cyc (not_root_inv hq0 hq1) hn]
  have hs : (∑ d ∈ n.divisors, (Nat.totient d : ℝ)) = n := by exact_mod_cast Nat.sum_totient n
  rw [hs]
  have hqn : q ^ n ≠ 1 := not_root hq1 n hn
  have h1 : |q ^ n - 1| = |1 - q ^ n| := abs_sub_comm _ _
  have h2 : q⁻¹ ^ n - 1 = q⁻¹ ^ n * (1 - q ^ n) := by
    rw [mul_sub, mul_one, ← mul_pow, inv_mul_cancel₀ hq0, one_pow]
  rw [h1, h2, abs_mul, Real.log_mul, abs_pow, abs_inv, Real.log_pow]
  · ring
  · exact abs_ne_zero.mpr (pow_ne_zero _ (inv_ne_zero hq0))
  · exact abs_ne_zero.mpr (sub_ne_zero.mpr (Ne.symm hqn))

theorem abs_cycG_le (hq1 : |q| < 1) {n : ℕ} (hn : 0 < n) :
    |cycG q n| ≤ 2 / (1 - |q|) * |q| ^ n := by
  have hle : |q ^ n| ≤ |q| := by
    rw [abs_pow]; exact pow_le_of_le_one (abs_nonneg q) hq1.le hn.ne'
  have e := abs_log_one_sub_le hq1 hle
  rw [abs_pow] at e
  unfold cycG
  rw [abs_mul, abs_two]
  calc 2 * |Real.log (|1 - q ^ n|)| ≤ 2 * (|q| ^ n / (1 - |q|)) := by linarith
    _ = _ := by ring

theorem sum_pow_le (hq1 : |q| < 1) (d : ℕ) : ∑ a ∈ Icc 1 d, |q| ^ a ≤ 1 / (1 - |q|) := by
  have hk : 0 < 1 - |q| := by linarith
  have h' := geom_sum_Ico_le_of_lt_one (m := 1) (n := d + 1) (abs_nonneg q) hq1
  have hI : Icc 1 d = Ico 1 (d + 1) := by ext; simp
  rw [hI]
  refine h'.trans ?_
  rw [pow_one]
  exact div_le_div_of_nonneg_right hq1.le hk.le

theorem abs_cycErr_le (hq0 : q ≠ 0) (hq1 : |q| < 1) {d : ℕ} (hd : 0 < d) :
    |cycErr q d| ≤ 2 / (1 - |q|) ^ 2 := by
  have hk : 0 < 1 - |q| := by linarith
  have hc : 0 ≤ 2 / (1 - |q|) := div_nonneg zero_le_two hk.le
  have hm := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.mp
    (fun n hn => sum_cycErr hq0 hq1 hn)) d hd
  rw [← hm, Nat.sum_divisorsAntidiagonal' (fun a b => (μ a : ℝ) * cycG q b)]
  calc |∑ a ∈ d.divisors, (μ (d / a) : ℝ) * cycG q a|
      ≤ ∑ a ∈ d.divisors, |(μ (d / a) : ℝ) * cycG q a| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ d.divisors, 2 / (1 - |q|) * |q| ^ a := by
      apply Finset.sum_le_sum
      intro a ha
      rw [abs_mul]
      have hmu : |(μ (d / a) : ℝ)| ≤ 1 := by
        exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d / a))
      calc _ ≤ 1 * |cycG q a| := mul_le_mul_of_nonneg_right hmu (abs_nonneg _)
        _ ≤ _ := by rw [one_mul]; exact abs_cycG_le hq1 (Nat.pos_of_mem_divisors ha)
    _ ≤ ∑ a ∈ Icc 1 d, 2 / (1 - |q|) * |q| ^ a := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro a ha
        exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors ha,
          Nat.le_of_dvd hd (Nat.dvd_of_mem_divisors ha)⟩
      · intro a _ _; exact mul_nonneg hc (pow_nonneg (abs_nonneg q) _)
    _ = 2 / (1 - |q|) * ∑ a ∈ Icc 1 d, |q| ^ a := by rw [Finset.mul_sum]
    _ ≤ 2 / (1 - |q|) * (1 / (1 - |q|)) := mul_le_mul_of_nonneg_left (sum_pow_le hq1 d) hc
    _ = _ := by rw [div_mul_div_comm, mul_one, sq]

/-- **Lemma 7, per factor**: `|Φ_ℓ(q) Φ_ℓ(1/q)| ≤ exp(2/(1 − |q|)²) |q|^{−φ(ℓ)}` for `ℓ ≥ 1`. -/
theorem norm_cyc_le (hq0 : q ≠ 0) (hq1 : |q| < 1) {ℓ : ℕ} (hℓ : 0 < ℓ) :
    |aeval q (cyclotomic ℓ ℤ) * aeval q⁻¹ (cyclotomic ℓ ℤ)| ≤
      Real.exp (2 / (1 - |q|) ^ 2) * (|q|⁻¹) ^ Nat.totient ℓ := by
  rw [aeval_cyc, aeval_cyc, abs_mul]
  have ha := abs_pos.mpr (cyc_eval_ne_zero (not_root hq1) hℓ)
  have hb := abs_pos.mpr (cyc_eval_ne_zero (not_root_inv hq0 hq1) hℓ)
  have hX : 0 < |q|⁻¹ := inv_pos.mpr (abs_pos.mpr hq0)
  have hE := (abs_le.mp (abs_cycErr_le hq0 hq1 hℓ)).2
  unfold cycErr at hE
  rw [← Real.exp_log (mul_pos ha hb), Real.log_mul ha.ne' hb.ne', ← Real.exp_log hX,
    ← Real.exp_nat_mul, ← Real.exp_add]
  exact Real.exp_le_exp.mpr (by linarith)

end QZeta3.Cost
