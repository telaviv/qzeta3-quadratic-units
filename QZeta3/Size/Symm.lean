import QZeta3.Statements

/-!
# Size: Lemma 1 (well-poised symmetry), A = 4, r = 1

PROOF_T1 §1, Lemma 1: `R(q^{-n}/T) = q^{2n} T^4 R(T)` (here `An/2 = 2n`), proved factor by factor.
-/

open Finset

namespace QZeta3.Size

variable {𝕜 : Type*} [Field 𝕜]

lemma qPoch_reflect (x q : 𝕜) (m : ℕ) :
    qPoch x q m = ∏ j ∈ range m, (1 - x * q ^ (m - 1 - j)) := by
  rw [qPoch, ← prod_range_reflect (fun i => 1 - x * q ^ i) m]

lemma prod_neg_inv (c q : 𝕜) (n : ℕ) :
    ∏ j ∈ range n, -(c * q ^ j)⁻¹ = (-1) ^ n * (c ^ n * ∏ j ∈ range n, q ^ j)⁻¹ := by
  have : ∀ j : ℕ, -(c * q ^ j)⁻¹ = (-1) * c⁻¹ * (q ^ j)⁻¹ := fun j => by rw [mul_inv]; ring
  simp only [this, prod_mul_distrib, prod_const, card_range, prod_inv_distrib]
  ring

lemma prod_pow_sq (q : 𝕜) (n : ℕ) :
    (∏ j ∈ range n, q ^ j) ^ 2 * q ^ n = (q ^ n) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [prod_range_succ]
    calc ((∏ j ∈ range n, q ^ j) * q ^ n) ^ 2 * q ^ (n + 1)
        = ((∏ j ∈ range n, q ^ j) ^ 2 * q ^ n) * q ^ n * q ^ (n + 1) := by ring
      _ = (q ^ n) ^ n * q ^ n * q ^ (n + 1) := by rw [ih]
      _ = (q ^ (n + 1)) ^ (n + 1) := by ring

lemma pow_aux {q : 𝕜} (hq : q ≠ 0) {n j : ℕ} (hj : j < n) :
    q ^ (n - 1 - j) = q ^ n * q ^ n / (q ^ (n + 1) * q ^ j) := by
  apply eq_div_of_mul_eq (mul_ne_zero (pow_ne_zero _ hq) (pow_ne_zero _ hq))
  rw [← pow_add, ← pow_add, ← pow_add]; congr 1; omega

variable {q T : 𝕜}

lemma D_symm (hq : q ≠ 0) (hT : T ≠ 0) (n : ℕ) :
    qPoch ((q ^ n)⁻¹ * T⁻¹) q (n + 1) =
      (∏ j ∈ range (n + 1), -(T * q ^ j)⁻¹) * qPoch T q (n + 1) := by
  rw [qPoch_reflect, qPoch, ← prod_mul_distrib]
  refine prod_congr rfl fun j hj => ?_
  have hj' : j ≤ n := by simp at hj; omega
  rw [show n + 1 - 1 - j = n - j by omega, pow_sub₀ q hq hj']
  have := pow_ne_zero j hq
  have := pow_ne_zero n hq
  field_simp
  ring

lemma A_symm (hq : q ≠ 0) (hT : T ≠ 0) (n : ℕ) :
    qPoch ((q ^ n)⁻¹ * ((q ^ n)⁻¹ * T⁻¹)) q n =
      (∏ j ∈ range n, -(q ^ (n + 1) * T * q ^ j)⁻¹) * qPoch (q ^ (n + 1) * T) q n := by
  rw [qPoch_reflect, qPoch, ← prod_mul_distrib]
  refine prod_congr rfl fun j hj => ?_
  have hj' : j < n := by simpa using hj
  rw [pow_aux hq hj']
  have := pow_ne_zero j hq
  have := pow_ne_zero n hq
  have := pow_ne_zero (n + 1) hq
  field_simp
  ring

lemma B_symm (hq : q ≠ 0) (hT : T ≠ 0) (n : ℕ) :
    qPoch (q ^ (n + 1) * ((q ^ n)⁻¹ * T⁻¹)) q n =
      (∏ j ∈ range n, -((q ^ n)⁻¹ * T * q ^ j)⁻¹) * qPoch ((q ^ n)⁻¹ * T) q n := by
  rw [qPoch_reflect, qPoch, ← prod_mul_distrib]
  refine prod_congr rfl fun j hj => ?_
  have hj' : j < n := by simpa using hj
  rw [pow_aux hq hj']
  have := pow_ne_zero j hq
  have := pow_ne_zero n hq
  have := pow_ne_zero (n + 1) hq
  field_simp
  ring

lemma key_scalar (hq : q ≠ 0) (hT : T ≠ 0) (n : ℕ) {P : 𝕜} (hP0 : P ≠ 0)
    (hP : P ^ 2 * q ^ n = (q ^ n) ^ n) :
    ((-1) ^ n * ((q ^ (n + 1) * T) ^ n * P)⁻¹) * ((-1) ^ n * (((q ^ n)⁻¹ * T) ^ n * P)⁻¹) *
        ((q ^ n)⁻¹ * T⁻¹) ^ n / ((-1) ^ (n + 1) * (T ^ (n + 1) * (P * q ^ n))⁻¹) ^ 4 =
      q ^ (2 * n) * T ^ 4 * T ^ n := by
  have hs1 : ((-1 : 𝕜) ^ n) * (-1) ^ n = 1 := by rw [← mul_pow]; norm_num
  have hs2 : ((-1 : 𝕜) ^ (n + 1)) ^ 4 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  calc _ = ((-1) ^ n * (-1) ^ n) / ((-1) ^ (n + 1)) ^ 4 *
        (((q ^ (n + 1) * T) ^ n * P)⁻¹ * (((q ^ n)⁻¹ * T) ^ n * P)⁻¹ *
          ((q ^ n)⁻¹ * T⁻¹) ^ n / ((T ^ (n + 1) * (P * q ^ n))⁻¹) ^ 4) := by ring
    _ = ((q ^ (n + 1) * T) ^ n * P)⁻¹ * (((q ^ n)⁻¹ * T) ^ n * P)⁻¹ *
          ((q ^ n)⁻¹ * T⁻¹) ^ n / ((T ^ (n + 1) * (P * q ^ n))⁻¹) ^ 4 := by
        rw [hs1, hs2]; ring
    _ = q ^ (2 * n) * T ^ 4 * T ^ n := by
        rw [pow_succ q n]
        simp only [mul_pow, inv_pow]
        rw [← hP]
        have := pow_ne_zero n hq
        field_simp
        ring

/-- **Lemma 1** (A = 4, r = 1): `R(q^{-n} T^{-1}) = q^{2n} T^4 R(T)`. -/
theorem Rfun_symm (hq : q ≠ 0) (hT : T ≠ 0) (n : ℕ) :
    Rfun n q ((q ^ n)⁻¹ * T⁻¹) = q ^ (2 * n) * T ^ 4 * Rfun n q T := by
  have hP0 : (∏ j ∈ range n, q ^ j) ≠ 0 := prod_ne_zero_iff.mpr fun j _ => pow_ne_zero _ hq
  have key := key_scalar hq hT n hP0 (prod_pow_sq q n)
  rw [← prod_neg_inv, ← prod_neg_inv, ← prod_range_succ (fun j => q ^ j) n,
    ← prod_neg_inv] at key
  rw [Rfun, Rfun, D_symm hq hT, A_symm hq hT, B_symm hq hT]
  linear_combination (qPoch q q n ^ 2 * qPoch ((q ^ n)⁻¹ * T) q n * qPoch (q ^ (n + 1) * T) q n /
    qPoch T q (n + 1) ^ 4) * key

end QZeta3.Size
