import QZeta3.Cost.Cyclo

/-!
# Lemma 7 (weak form): the frozen `CostBound`

* `totient_two_mul_le`: `φ(2m) ≤ m`;
* `eight_sum_totient_le`: `8 ∑_{ℓ ≤ n} φ(ℓ) ≤ 3 (n + 1)²` (sieve at the prime 2: `φ(ℓ) ≤ ℓ`, `φ(2m) ≤ m`);
* `abs_dn_mul_le`: `|d_n(q) d_n(1/q)| ≤ exp(M)ⁿ |q|^{−∑_{ℓ ≤ n} φ(ℓ)}`, `M = 2/(1 − |q|)²` (from `norm_cyc_le`);
* `costBound : CostBound`, with `C = exp(M)⁸`.
-/

open Polynomial Finset

namespace QZeta3.Cost

/-! ### The totient sum, sieved at 2 -/

theorem totient_two_mul_le (m : ℕ) : Nat.totient (2 * m) ≤ m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.even_or_odd m with hm | hm
    · rw [Nat.totient_two_mul_of_even hm]
      obtain ⟨k, rfl⟩ := hm
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp
      · have := ih k (by omega)
        rw [show k + k = 2 * k by ring]
        omega
    · rw [Nat.totient_two_mul_of_odd hm]
      exact Nat.totient_le m

theorem eight_sum_totient_le (n : ℕ) : 8 * ∑ ℓ ∈ Icc 1 n, Nat.totient ℓ ≤ 3 * (n + 1) ^ 2 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => simp
    | 1, _ => simp
    | m + 2, ih =>
      have h := ih m (by omega)
      rw [show m + 2 = m + 1 + 1 from rfl, Finset.sum_Icc_succ_top (by omega),
        Finset.sum_Icc_succ_top (by omega)]
      have e : 3 * (m + 1 + 1 + 1) ^ 2 = 3 * (m + 1) ^ 2 + 12 * m + 24 := by ring
      rw [e]
      generalize (m + 1) ^ 2 = A at h ⊢
      rcases Nat.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
      · have h1 := Nat.totient_le (m + 1)
        have h2 := totient_two_mul_le (k + 1)
        rw [show 2 * (k + 1) = m + 1 + 1 by omega] at h2
        omega
      · have h1 := totient_two_mul_le (k + 1)
        rw [show 2 * (k + 1) = m + 1 by omega] at h1
        have h2 := Nat.totient_le (m + 1 + 1)
        omega

/-! ### The product over `ℓ ≤ n` -/

theorem abs_dn_mul_le {q : ℝ} (hq0 : q ≠ 0) (hq1 : |q| < 1) (n : ℕ) :
    |dn n q * dn n q⁻¹| ≤
      Real.exp (2 / (1 - |q|) ^ 2) ^ n * (|q|⁻¹) ^ (∑ ℓ ∈ Icc 1 n, Nat.totient ℓ) := by
  unfold dn
  rw [← Finset.prod_mul_distrib, Finset.abs_prod]
  calc ∏ ℓ ∈ Icc 1 n, |aeval q (cyclotomic ℓ ℤ) * aeval q⁻¹ (cyclotomic ℓ ℤ)|
      ≤ ∏ ℓ ∈ Icc 1 n, (Real.exp (2 / (1 - |q|) ^ 2) * (|q|⁻¹) ^ Nat.totient ℓ) := by
        apply Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
        intro ℓ hℓ
        exact norm_cyc_le hq0 hq1 (by simp only [mem_Icc] at hℓ; omega)
    _ = _ := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Icc, Nat.add_sub_cancel,
          Finset.prod_pow_eq_pow_sum]

/-- **Lemma 7** (weak form, constant `3/8`), the frozen `CostBound`. -/
theorem costBound : CostBound := by
  intro q hq0 hq1
  refine ⟨Real.exp (2 / (1 - |q|) ^ 2) ^ 8, fun n _ => ?_⟩
  have hX : 1 ≤ |q|⁻¹ := (one_le_inv₀ (abs_pos.mpr hq0)).mpr hq1.le
  have hS := eight_sum_totient_le n
  set S := ∑ ℓ ∈ Icc 1 n, Nat.totient ℓ
  set E := Real.exp (2 / (1 - |q|) ^ 2)
  calc |dn n q * dn n q⁻¹| ^ 8 ≤ (E ^ n * (|q|⁻¹) ^ S) ^ 8 :=
        pow_le_pow_left₀ (abs_nonneg _) (abs_dn_mul_le hq0 hq1 n) 8
    _ = (E ^ 8) ^ n * (|q|⁻¹) ^ (8 * S) := by ring
    _ ≤ (E ^ 8) ^ n * (|q|⁻¹) ^ (3 * (n + 1) ^ 2) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hX hS) (by positivity)

end QZeta3.Cost
