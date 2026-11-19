import QZeta3.Denom.Lagrange

/-!
# The simple partial-fraction weights are integer Laurent polynomials

The three numerators of PROOF_T1 Lemma 3 (A = 4, r = 1):
* `N1 = (x;x)_n` (types 1 and 2, the constant polynomial),
* `N3 = (x^{−n} T; x)_n`, `N4 = (x^{n+1} T; x)_n`.
Their weights `wt_{j'} = N_i(x^{−j'}) / den_{j'}` are, with `U⁻¹ = Ui`:
* `wt(N1) = Ui · [n, j']`,
* `wt(N3) = Ui · V · [j'+n, j'] · [n, j']`, `V = ∏_{i<n} (−x^{−(j'+1+i)})`,
* `wt(N4) = Ui · [n−j'+n, n−j'] · [n, j']`.
Hence each weight is `LaurentInt` (uniformly in `x`).
-/

open Polynomial Finset

namespace QZeta3.Denom

/-- The numerator of the type-1 factors: the constant `(x;x)_n`. -/
noncomputable def N1 (n : ℕ) (x : ℝ) : ℝ[X] := C (qPoch x x n)

/-- `(x^{−n} T; x)_n`. -/
noncomputable def N3 (n : ℕ) (x : ℝ) : ℝ[X] := qPochPoly (x ^ n)⁻¹ x n

/-- `(x^{n+1} T; x)_n`. -/
noncomputable def N4 (n : ℕ) (x : ℝ) : ℝ[X] := qPochPoly (x ^ (n + 1)) x n

theorem natDegree_qPochPoly_le (y x : ℝ) (m : ℕ) : (qPochPoly y x m).natDegree ≤ m := by
  unfold qPochPoly
  refine (natDegree_prod_le _ _).trans ?_
  refine (sum_le_sum fun i _ => natDegree_one_sub_C_mul_X_le (y * x ^ i)).trans ?_
  simp

theorem natDegree_N1 (n : ℕ) (x : ℝ) : (N1 n x).natDegree ≤ n := by simp [N1]

theorem natDegree_N3 (n : ℕ) (x : ℝ) : (N3 n x).natDegree ≤ n := natDegree_qPochPoly_le _ _ _

theorem natDegree_N4 (n : ℕ) (x : ℝ) : (N4 n x).natDegree ≤ n := natDegree_qPochPoly_le _ _ _

theorem eval_qPochPoly (y x t : ℝ) (m : ℕ) :
    (qPochPoly y x m).eval t = ∏ i ∈ range m, (1 - y * x ^ i * t) := by
  simp [qPochPoly, eval_prod]

/-- `V = ∏_{i<n} (−x^{−(j'+1+i)})`. -/
noncomputable def Vf (x : ℝ) (n j' : ℕ) : ℝ := ∏ i ∈ range n, (-(x ^ (j' + 1 + i))⁻¹)

theorem Vf_laurent (n j' : ℕ) : LaurentInt (fun x => Vf x n j') :=
  LaurentInt.prod _ fun i _ => (LaurentInt.inv_pow_id (j' + 1 + i)).neg

theorem one_sub_aux3 {a b c : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    1 - (a * b)⁻¹ * a * c⁻¹ = -(c * b)⁻¹ * (1 - c * b) := by
  have h1 : (a * b)⁻¹ * a = b⁻¹ := by
    rw [mul_inv, mul_comm a⁻¹, mul_assoc, inv_mul_cancel₀ ha, mul_one]
  have h3 : c⁻¹ * c = 1 := inv_mul_cancel₀ hc
  have h4 : b⁻¹ * b = 1 := inv_mul_cancel₀ hb
  rw [h1, mul_inv c b]
  linear_combination (-(b⁻¹ * b)) * h3 - h4

theorem Uf_ne_zero {x : ℝ} (hx : x ≠ 0) (j' : ℕ) : Uf x j' ≠ 0 :=
  left_ne_zero_of_mul_eq_one (Uf_mul_Ui hx j')

theorem den_ne_zero' {x : ℝ} (hx : x ≠ 0) (hx1 : |x| ≠ 1) (j' m : ℕ) :
    Uf x j' * qPoch x x j' * qPoch x x m ≠ 0 :=
  mul_ne_zero (mul_ne_zero (Uf_ne_zero hx j') (qPoch_ne_zero hx hx1 j')) (qPoch_ne_zero hx hx1 m)

theorem wt_N1 {x : ℝ} (hx : x ≠ 0) (hx1 : |x| ≠ 1) {n j' : ℕ} (hj : j' ≤ n) :
    wt n x (N1 n x) j' = Ui x j' * aeval x (gauss n j') := by
  obtain ⟨m, rfl⟩ : ∃ m, n = j' + m := ⟨n - j', by omega⟩
  rw [wt, N1, eval_C, den_eq hx hj, Nat.add_sub_cancel_left, div_eq_iff (den_ne_zero' hx hx1 j' m),
    ← gauss_mul x j' m]
  have hUU := Uf_mul_Ui hx j'
  linear_combination (-(qPoch x x j' * qPoch x x m * aeval x (gauss (j' + m) j'))) * hUU

theorem wt_N3 {x : ℝ} (hx : x ≠ 0) (hx1 : |x| ≠ 1) {n j' : ℕ} (hj : j' ≤ n) :
    wt n x (N3 n x) j' =
      Ui x j' * Vf x n j' * aeval x (gauss (j' + n) j') * aeval x (gauss n j') := by
  have hE : (N3 n x).eval (x ^ j')⁻¹ = Vf x n j' * ∏ i ∈ range n, (1 - x ^ (j' + 1 + i)) := by
    rw [N3, eval_qPochPoly, ← prod_range_reflect (fun i => 1 - (x ^ n)⁻¹ * x ^ i * (x ^ j')⁻¹) n,
      Vf, ← prod_mul_distrib]
    refine prod_congr rfl fun i hi => ?_
    have hi' := mem_range.1 hi
    have e1 : x ^ n = x ^ (n - 1 - i) * x ^ (i + 1) := by rw [← pow_add]; congr 1; omega
    have e2 : x ^ (j' + 1 + i) = x ^ j' * x ^ (i + 1) := by rw [← pow_add]; congr 1; omega
    rw [e1, e2]
    exact one_sub_aux3 (pow_ne_zero _ hx) (pow_ne_zero _ hx) (pow_ne_zero _ hx)
  have hP : ∏ i ∈ range n, (1 - x ^ (j' + 1 + i)) = qPoch x x n * aeval x (gauss (j' + n) j') := by
    apply mul_left_cancel₀ (qPoch_ne_zero hx hx1 j')
    rw [← qPoch_add, ← mul_assoc, gauss_mul]
  obtain ⟨m, rfl⟩ : ∃ m, n = j' + m := ⟨n - j', by omega⟩
  have h3 := gauss_mul x j' m
  have hUU := Uf_mul_Ui hx j'
  rw [wt, hE, den_eq hx hj, Nat.add_sub_cancel_left, div_eq_iff (den_ne_zero' hx hx1 j' m), hP]
  linear_combination (-(Vf x (j' + m) j' * aeval x (gauss (j' + (j' + m)) j'))) * h3 -
    Vf x (j' + m) j' * aeval x (gauss (j' + (j' + m)) j') * qPoch x x j' * qPoch x x m *
      aeval x (gauss (j' + m) j') * hUU

theorem wt_N4 {x : ℝ} (hx : x ≠ 0) (hx1 : |x| ≠ 1) {n j' : ℕ} (hj : j' ≤ n) :
    wt n x (N4 n x) j' =
      Ui x j' * aeval x (gauss (n - j' + n) (n - j')) * aeval x (gauss n j') := by
  obtain ⟨m, rfl⟩ : ∃ m, n = j' + m := ⟨n - j', by omega⟩
  have hE : (N4 (j' + m) x).eval (x ^ j')⁻¹ = ∏ i ∈ range (j' + m), (1 - x ^ (m + 1 + i)) := by
    rw [N4, eval_qPochPoly]
    refine prod_congr rfl fun i _ => ?_
    have e : x ^ (j' + m + 1) * x ^ i = x ^ j' * x ^ (m + 1 + i) := by
      rw [← pow_add, ← pow_add]; congr 1; omega
    rw [e, mul_comm (x ^ j'), mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hx), mul_one]
  have hP : ∏ i ∈ range (j' + m), (1 - x ^ (m + 1 + i)) =
      qPoch x x (j' + m) * aeval x (gauss (m + (j' + m)) m) := by
    apply mul_left_cancel₀ (qPoch_ne_zero hx hx1 m)
    rw [← qPoch_add, ← mul_assoc, gauss_mul]
  have h3 := gauss_mul x j' m
  have hUU := Uf_mul_Ui hx j'
  rw [wt, hE, den_eq hx hj, Nat.add_sub_cancel_left, div_eq_iff (den_ne_zero' hx hx1 j' m), hP]
  linear_combination (-(aeval x (gauss (m + (j' + m)) m))) * h3 -
    aeval x (gauss (m + (j' + m)) m) * qPoch x x j' * qPoch x x m *
      aeval x (gauss (j' + m) j') * hUU

theorem wt_N1_laurent {n j' : ℕ} (hj : j' ≤ n) : LaurentInt (fun x => wt n x (N1 n x) j') :=
  ((Ui_laurent j').mul (LaurentInt.aeval _)).congr fun _ hx hx1 => (wt_N1 hx hx1 hj).symm

theorem wt_N3_laurent {n j' : ℕ} (hj : j' ≤ n) : LaurentInt (fun x => wt n x (N3 n x) j') :=
  ((((Ui_laurent j').mul (Vf_laurent n j')).mul (LaurentInt.aeval _)).mul
    (LaurentInt.aeval _)).congr fun _ hx hx1 => (wt_N3 hx hx1 hj).symm

theorem wt_N4_laurent {n j' : ℕ} (hj : j' ≤ n) : LaurentInt (fun x => wt n x (N4 n x) j') :=
  (((Ui_laurent j').mul (LaurentInt.aeval _)).mul (LaurentInt.aeval _)).congr
    fun _ hx hx1 => (wt_N4 hx hx1 hj).symm

end QZeta3.Denom
