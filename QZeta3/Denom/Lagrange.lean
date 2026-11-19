import QZeta3.Denom.Gauss

/-!
# Simple partial fractions of a polynomial of degree ≤ n

For a polynomial `N` of degree `≤ n` and an admissible real `x`,
  `N(T) = Σ_{j' ≤ n} wt_{j'} · ∏_{j'' ≠ j'} (1 − x^{j''} T)`,  `wt_{j'} = N(x^{−j'}) / den_{j'}`,
with `den_{j'} = ∏_{j'' ≠ j'} (1 − x^{j''−j'})` (PROOF_T1 Lemma 3, "each f_i is proper with simple
poles"). Both sides have degree `≤ n` and agree at the `n + 1` distinct points `x^{−j'}`.

We also factor `den_{j'} = U_{j'} · (x;x)_{j'} · (x;x)_{n−j'}` with `U_{j'} = ∏_{i<j'} (−x^{−(i+1)})`.
-/

open Polynomial Finset

namespace QZeta3.Denom

/-- `∏_{j'' ≤ n, j'' ≠ j'} (1 − x^{j''} x^{−j'})`. -/
noncomputable def den (n : ℕ) (x : ℝ) (j' : ℕ) : ℝ :=
  ∏ j'' ∈ (range (n + 1)).erase j', (1 - x ^ j'' * (x ^ j')⁻¹)

/-- The weight of `∏_{j'' ≠ j'} (1 − x^{j''} T)` in the interpolation of `N`. -/
noncomputable def wt (n : ℕ) (x : ℝ) (N : ℝ[X]) (j' : ℕ) : ℝ := N.eval (x ^ j')⁻¹ / den n x j'

/-- `∏_{j'' ≤ n, j'' ≠ j'} (1 − x^{j''} T)`. -/
noncomputable def lagPoly (n : ℕ) (x : ℝ) (j' : ℕ) : ℝ[X] :=
  ∏ j'' ∈ (range (n + 1)).erase j', (1 - C (x ^ j'') * X)

theorem den_ne_zero {x : ℝ} (hx : x ≠ 0) (hx1 : |x| ≠ 1) (n j' : ℕ) : den n x j' ≠ 0 :=
  prod_ne_zero_iff.2 fun _ hj'' => one_sub_pow_mul_inv_ne_zero hx hx1 (mem_erase.1 hj'').1

theorem natDegree_one_sub_C_mul_X_le (c : ℝ) : (1 - C c * X).natDegree ≤ 1 :=
  (natDegree_sub_le _ _).trans (max_le (by simp) ((natDegree_C_mul_le _ _).trans natDegree_X_le))

theorem natDegree_lagPoly_le (n : ℕ) (x : ℝ) {j' : ℕ} (hj : j' ∈ range (n + 1)) :
    (lagPoly n x j').natDegree ≤ n := by
  unfold lagPoly
  refine (natDegree_prod_le _ _).trans ?_
  refine (sum_le_sum fun i _ => natDegree_one_sub_C_mul_X_le (x ^ i)).trans (le_of_eq ?_)
  rw [sum_const, card_erase_of_mem hj, card_range, smul_eq_mul, mul_one, Nat.add_sub_cancel]

theorem lagrange {x : ℝ} (hx : x ≠ 0) (hx1 : |x| ≠ 1) (n : ℕ) (N : ℝ[X])
    (hN : N.natDegree ≤ n) :
    N = ∑ j' ∈ range (n + 1), C (wt n x N j') * lagPoly n x j' := by
  have hinj : Set.InjOn (fun j : ℕ => (x ^ j)⁻¹) (range (n + 1)) :=
    fun a _ b _ h => pow_inj_of_adm hx hx1 (inv_inj.1 h)
  apply eq_of_degree_sub_lt_of_eval_finset_eq ((range (n + 1)).image fun j => (x ^ j)⁻¹)
  · rw [card_image_of_injOn hinj, card_range]
    have h2 : (∑ j' ∈ range (n + 1), C (wt n x N j') * lagPoly n x j').natDegree ≤ n :=
      natDegree_sum_le_of_forall_le _ _ fun j' hj' =>
        (natDegree_C_mul_le _ _).trans (natDegree_lagPoly_le n x hj')
    have h3 := natDegree_sub_le_of_le hN h2
    rw [max_self] at h3
    exact (degree_le_of_natDegree_le h3).trans_lt (by exact_mod_cast Nat.lt_succ_self n)
  · intro y hy
    obtain ⟨k, hk, rfl⟩ := mem_image.1 hy
    rw [eval_finsetSum, sum_eq_single k]
    · rw [eval_mul, eval_C, lagPoly, eval_prod, wt]
      simp only [eval_sub, eval_one, eval_mul, eval_C, eval_X]
      rw [show (∏ j'' ∈ (range (n + 1)).erase k, (1 - x ^ j'' * (x ^ k)⁻¹)) = den n x k from rfl,
        div_mul_cancel₀ _ (den_ne_zero hx hx1 n k)]
    · intro j' _ hjk
      rw [eval_mul, lagPoly, eval_prod]
      apply mul_eq_zero_of_right
      exact prod_eq_zero (mem_erase.2 ⟨Ne.symm hjk, hk⟩)
        (by simp [mul_inv_cancel₀ (pow_ne_zero k hx)])
    · intro h; exact absurd hk h

/-- Splitting a product over `{0, …, n} \ {j}` at `j`. -/
theorem prod_erase_split (f : ℕ → ℝ) {n j : ℕ} (hj : j ≤ n) :
    ∏ i ∈ (range (n + 1)).erase j, f i =
      (∏ i ∈ range j, f i) * ∏ i ∈ range (n - j), f (j + 1 + i) := by
  have h1 : ∏ i ∈ (range (n + 1)).erase j, f i =
      ∏ i ∈ range (n + 1), (if i = j then 1 else f i) := by
    rw [← prod_erase (range (n + 1)) (f := fun i => if i = j then 1 else f i) (a := j) (by simp)]
    exact prod_congr rfl fun i hi => by simp [(mem_erase.1 hi).1]
  rw [h1, show n + 1 = (j + 1) + (n - j) by omega, prod_range_add, prod_range_succ]
  rw [ite_eq_left rfl, mul_one]
  congr 1
  · exact prod_congr rfl fun i hi => by rw [ite_eq_right (mem_range.1 hi).ne]
  · exact prod_congr rfl fun i _ => by rw [ite_eq_right (show j + 1 + i ≠ j by omega)]

/-- `U_{j'} = ∏_{i<j'} (−x^{−(i+1)})`. -/
noncomputable def Uf (x : ℝ) (j' : ℕ) : ℝ := ∏ i ∈ range j', (-(x ^ (i + 1))⁻¹)

/-- `U_{j'}⁻¹ = ∏_{i<j'} (−x^{i+1})`. -/
noncomputable def Ui (x : ℝ) (j' : ℕ) : ℝ := ∏ i ∈ range j', (-(x ^ (i + 1)))

theorem Uf_mul_Ui {x : ℝ} (hx : x ≠ 0) (j' : ℕ) : Uf x j' * Ui x j' = 1 := by
  rw [Uf, Ui, ← prod_mul_distrib]
  exact prod_eq_one fun i _ => by rw [neg_mul_neg, inv_mul_cancel₀ (pow_ne_zero _ hx)]

theorem Ui_laurent (j' : ℕ) : LaurentInt (fun x => Ui x j') :=
  LaurentInt.prod _ fun i _ => (LaurentInt.pow_id (i + 1)).neg

theorem one_sub_aux {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) : 1 - a * (a * b)⁻¹ = -b⁻¹ * (1 - b) := by
  have h1 : a * (a * b)⁻¹ = b⁻¹ := by rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ ha, one_mul]
  have h2 : b⁻¹ * b = 1 := inv_mul_cancel₀ hb
  rw [h1]
  linear_combination (-1 : ℝ) * h2

theorem den_eq {x : ℝ} (hx : x ≠ 0) {n j' : ℕ} (hj : j' ≤ n) :
    den n x j' = Uf x j' * qPoch x x j' * qPoch x x (n - j') := by
  have hA : ∏ i ∈ range j', (1 - x ^ i * (x ^ j')⁻¹) = Uf x j' * qPoch x x j' := by
    rw [← prod_range_reflect (fun i => 1 - x ^ i * (x ^ j')⁻¹) j', Uf, qPoch_eq_prod,
      ← prod_mul_distrib]
    refine prod_congr rfl fun i hi => ?_
    have hi' := mem_range.1 hi
    have e : x ^ j' = x ^ (j' - 1 - i) * x ^ (i + 1) := by rw [← pow_add]; congr 1; omega
    rw [e, one_sub_aux (pow_ne_zero _ hx) (pow_ne_zero _ hx)]
  have hB : ∏ i ∈ range (n - j'), (1 - x ^ (j' + 1 + i) * (x ^ j')⁻¹) = qPoch x x (n - j') := by
    rw [qPoch_eq_prod]
    refine prod_congr rfl fun i _ => ?_
    rw [show j' + 1 + i = j' + (i + 1) by omega, pow_add x j' (i + 1), mul_comm (x ^ j'), mul_assoc,
      mul_inv_cancel₀ (pow_ne_zero _ hx), mul_one]
  rw [den, prod_erase_split _ hj, hA, hB]

end QZeta3.Denom
