import QZeta3.Denom.Laurent

/-!
# `d_n` and the factors `1 − x^m`

`d_n(x) = ∏_{ℓ=1}^{n} Φ_ℓ(x)` is an integer polynomial, and for `1 ≤ m ≤ n` it is divisible by
`x^m − 1 = ∏_{ℓ ∣ m} Φ_ℓ(x)`. Hence `d_n/(1 − x^m)` and `d_n/(1 − x^{−m})` are `LaurentInt`
(PROOF_T1 §2, before Lemma 3).
-/

open Polynomial Finset

namespace QZeta3.Denom

theorem dn_laurent (n : ℕ) : LaurentInt (dn n) :=
  ⟨∏ ℓ ∈ Icc 1 n, cyclotomic ℓ ℤ, 0, fun x _ _ => by simp [dn, map_prod]⟩

theorem dn_eq_mul (n m : ℕ) (hm1 : 1 ≤ m) (hmn : m ≤ n) (x : ℝ) :
    dn n x = (x ^ m - 1) * Polynomial.aeval x (∏ ℓ ∈ Icc 1 n \ m.divisors, cyclotomic ℓ ℤ) := by
  have hsub : m.divisors ⊆ Icc 1 n := fun d hd => by
    rw [Nat.mem_divisors] at hd
    rw [mem_Icc]
    exact ⟨Nat.pos_of_dvd_of_pos hd.1 (by omega), (Nat.le_of_dvd (by omega) hd.1).trans hmn⟩
  have hcyc : ∏ ℓ ∈ m.divisors, Polynomial.aeval x (cyclotomic ℓ ℤ) = x ^ m - 1 := by
    have := congrArg (Polynomial.aeval x) (prod_cyclotomic_eq_X_pow_sub_one (show 0 < m by omega) ℤ)
    simpa [map_prod] using this
  unfold dn
  rw [← prod_sdiff hsub, hcyc, map_prod]
  ring

theorem dn_div (n m : ℕ) (hm1 : 1 ≤ m) (hmn : m ≤ n) :
    LaurentInt (fun x => dn n x * (1 - x ^ m)⁻¹) := by
  refine ⟨-∏ ℓ ∈ Icc 1 n \ m.divisors, cyclotomic ℓ ℤ, 0, fun x hx hx1 => ?_⟩
  have hne := one_sub_pow_ne_zero hx hx1 (m := m) (by omega)
  have h' : (x ^ m - 1) * (1 - x ^ m)⁻¹ = -1 := by
    have e : x ^ m - 1 = -(1 - x ^ m) := by ring
    rw [e, neg_mul, mul_inv_cancel₀ hne]
  beta_reduce
  rw [dn_eq_mul n m hm1 hmn x, pow_zero, one_mul, map_neg, mul_right_comm, h']
  ring

theorem dn_div_inv (n m : ℕ) (hm1 : 1 ≤ m) (hmn : m ≤ n) :
    LaurentInt (fun x => dn n x * (1 - (x ^ m)⁻¹)⁻¹) := by
  refine ((LaurentInt.pow_id m).mul (dn_div n m hm1 hmn)).neg.congr fun x hx hx1 => ?_
  have hne := one_sub_pow_ne_zero hx hx1 (m := m) (by omega)
  have hxm : x ^ m ≠ 0 := pow_ne_zero _ hx
  have key : (1 - (x ^ m)⁻¹)⁻¹ = -(x ^ m * (1 - x ^ m)⁻¹) := by
    apply inv_eq_of_mul_eq_one_right
    have h1 : (x ^ m)⁻¹ * x ^ m = 1 := inv_mul_cancel₀ hxm
    have h2 : (1 - x ^ m) * (1 - x ^ m)⁻¹ = 1 := mul_inv_cancel₀ hne
    linear_combination (1 - x ^ m)⁻¹ * h1 + h2
  rw [key]
  ring

/-- `d_n · (1 − x^{a} x^{−b})⁻¹` is `LaurentInt` for `a ≠ b`, both `≤ n`. -/
theorem dn_div_ratio (n a b : ℕ) (ha : a ≤ n) (hb : b ≤ n) (hab : a ≠ b) :
    LaurentInt (fun x => dn n x * (1 - x ^ a * (x ^ b)⁻¹)⁻¹) := by
  rcases lt_or_gt_of_ne hab with h | h
  · refine (dn_div_inv n (b - a) (by omega) (by omega)).congr fun x hx _ => ?_
    have : x ^ b = x ^ a * x ^ (b - a) := by rw [← pow_add]; congr 1; omega
    rw [this, mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hx), one_mul]
  · refine (dn_div n (a - b) (by omega) (by omega)).congr fun x hx _ => ?_
    have : x ^ a = x ^ (a - b) * x ^ b := by rw [← pow_add]; congr 1; omega
    rw [this, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hx), mul_one]

end QZeta3.Denom
