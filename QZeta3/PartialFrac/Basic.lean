import QZeta3.Statements

/-!
# Partial fractions (2.1): polynomial helpers

Notation (PROOF_T1 §2): `Lin q j = 1 − q^j T`, `Dpoly = ∏_{j ≤ n} (1 − q^j T)⁴`,
`Oth n q j = ∏_{j' ≠ j} (1 − q^{j'} T)⁴`, `Qpoly n q j = Σ_s c_{s,j} u^{4−s}`, and
`Hpoly = N − Σ_{j,s} c_{s,j} (1 − q^j T)^{4−s} ∏_{j' ≠ j} (1 − q^{j'} T)⁴`.
-/

open Polynomial Finset

namespace QZeta3.PartialFrac

noncomputable section

variable {𝕜 : Type*} [Field 𝕜]

/-- `1 − q^j T`. -/
def Lin (q : 𝕜) (j : ℕ) : 𝕜[X] := 1 - C (q ^ j) * X

/-- `∏_{j' ≠ j, j' ≤ n} (1 − q^{j'} T)⁴`. -/
def Oth (n : ℕ) (q : 𝕜) (j : ℕ) : 𝕜[X] := ∏ j' ∈ (range (n + 1)).erase j, Lin q j' ^ 4

/-- `D(T) = ∏_{j ≤ n} (1 − q^j T)⁴`. -/
def Dpoly (n : ℕ) (q : 𝕜) : 𝕜[X] := ∏ j ∈ range (n + 1), Lin q j ^ 4

/-- `Q_j(u) = Σ_{s=1}^{4} c_{s,j} u^{4−s}`, the principal part at the pole `q^{−j}`. -/
def Qpoly (n : ℕ) (q : 𝕜) (j : ℕ) : 𝕜[X] := ∑ s ∈ Icc 1 4, C (cc n q s j) * X ^ (4 - s)

/-- `H = N − Σ_{j,s} c_{s,j} (1 − q^j T)^{4−s} ∏_{j' ≠ j} (1 − q^{j'} T)⁴`. -/
def Hpoly (n : ℕ) (q : 𝕜) : 𝕜[X] :=
  Npoly n q - ∑ j ∈ range (n + 1), ∑ s ∈ Icc 1 4, C (cc n q s j) * (Lin q j ^ (4 - s) * Oth n q j)

/-! ### Substitutions -/

lemma lin_comp (q : 𝕜) (j : ℕ) (p : 𝕜[X]) : (Lin q j).comp p = 1 - C (q ^ j) * p := by
  simp only [Lin, sub_comp, one_comp, mul_comp, C_comp, X_comp]

lemma lin_comp_tsub {q : 𝕜} (hq : q ≠ 0) (j : ℕ) : (Lin q j).comp (Tsub q j) = X := by
  have h : q ^ j ≠ 0 := pow_ne_zero _ hq
  rw [lin_comp, Tsub, ← mul_assoc, ← C_mul, mul_inv_cancel₀ h, C_1, one_mul, sub_sub_cancel]

lemma tsub_comp_lin {q : 𝕜} (hq : q ≠ 0) (j : ℕ) : (Tsub q j).comp (Lin q j) = X := by
  have h : q ^ j ≠ 0 := pow_ne_zero _ hq
  simp only [Lin, Tsub, sub_comp, one_comp, mul_comp, C_comp, X_comp]
  rw [sub_sub_cancel, ← mul_assoc, ← C_mul, inv_mul_cancel₀ h, C_1, one_mul]

lemma oth_comp_tsub (n : ℕ) (q : 𝕜) (j : ℕ) : (Oth n q j).comp (Tsub q j) = Dother n q j := by
  simp only [Oth, Dother, Polynomial.prod_comp, pow_comp, lin_comp]

/-- Pull back `u⁴ ∣ H(T(u))` to `(1 − q^j T)⁴ ∣ H(T)`. -/
lemma lin_pow_dvd_of_comp {q : 𝕜} (hq : q ≠ 0) (j : ℕ) {H : 𝕜[X]}
    (h : X ^ 4 ∣ H.comp (Tsub q j)) : Lin q j ^ 4 ∣ H := by
  obtain ⟨K, hK⟩ := h
  have e : H = (H.comp (Tsub q j)).comp (Lin q j) := by
    rw [comp_assoc, tsub_comp_lin hq, comp_X]
  rw [e, hK, mul_comp, pow_comp, X_comp]
  exact dvd_mul_right _ _

/-! ### Coprimality -/

lemma one_sub_coprime {a b : 𝕜} (h : a ≠ b) :
    IsCoprime (1 - C a * X : 𝕜[X]) (1 - C b * X) := by
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  refine ⟨C (b / (b - a)), C (-a / (b - a)), ?_⟩
  have h1 : b / (b - a) + -a / (b - a) = 1 := by
    rw [← add_div, div_eq_one_iff_eq hba]; ring
  have h2 : b / (b - a) * a + -a / (b - a) * b = 0 := by ring
  calc C (b / (b - a)) * (1 - C a * X) + C (-a / (b - a)) * (1 - C b * X)
      = C (b / (b - a) + -a / (b - a)) - C (b / (b - a) * a + -a / (b - a) * b) * X := by
        simp only [C_add, C_mul]; ring
    _ = 1 := by rw [h1, h2, C_1, C_0, zero_mul, sub_zero]

lemma lin_pow_coprime {q : 𝕜} {i k : ℕ} (h : q ^ i ≠ q ^ k) :
    IsCoprime (Lin q i ^ 4) (Lin q k ^ 4) :=
  (one_sub_coprime h).pow

/-! ### Degrees -/

lemma natDegree_one_sub_le (a : 𝕜) : (1 - C a * X : 𝕜[X]).natDegree ≤ 1 := by
  have e : (1 - C a * X : 𝕜[X]) = C (-a) * X + C 1 := by simp only [C_neg, C_1]; ring
  rw [e]; exact natDegree_linear_le

lemma natDegree_lin_le (q : 𝕜) (j : ℕ) : (Lin q j).natDegree ≤ 1 := natDegree_one_sub_le _

lemma natDegree_lin {q : 𝕜} (hq : q ≠ 0) (j : ℕ) : (Lin q j).natDegree = 1 := by
  have e : Lin q j = C (-(q ^ j)) * X + C 1 := by simp only [Lin, C_neg, C_1]; ring
  rw [e]; exact natDegree_linear (neg_ne_zero.mpr (pow_ne_zero _ hq))

lemma lin_ne_zero {q : 𝕜} (hq : q ≠ 0) (j : ℕ) : Lin q j ≠ 0 := by
  intro h
  have := natDegree_lin hq j
  rw [h, natDegree_zero] at this
  exact absurd this (by norm_num)

lemma natDegree_qPochPoly_le (y q : 𝕜) (m : ℕ) : (qPochPoly y q m).natDegree ≤ m := by
  unfold qPochPoly
  have h : ∑ i ∈ range m, (1 - C (y * q ^ i) * X).natDegree ≤ ∑ _i ∈ range m, (1 : ℕ) :=
    sum_le_sum fun i _ => natDegree_one_sub_le (y * q ^ i)
  have h2 : ∑ _i ∈ range m, (1 : ℕ) = m := by simp
  exact (natDegree_prod_le (range m) (fun i => 1 - C (y * q ^ i) * X)).trans (h.trans h2.le)

lemma natDegree_npoly_le (n : ℕ) (q : 𝕜) : (Npoly n q).natDegree ≤ 3 * n := by
  unfold Npoly
  have h1 := natDegree_qPochPoly_le (q ^ n)⁻¹ q n
  have h2 := natDegree_qPochPoly_le (q ^ (n + 1)) q n
  have e1 := natDegree_C_mul_le (qPoch q q n ^ 2) (qPochPoly (q ^ n)⁻¹ q n)
  have e2 := natDegree_mul_le (p := C (qPoch q q n ^ 2) * qPochPoly (q ^ n)⁻¹ q n)
    (q := qPochPoly (q ^ (n + 1)) q n)
  have e3 := natDegree_mul_le
    (p := C (qPoch q q n ^ 2) * qPochPoly (q ^ n)⁻¹ q n * qPochPoly (q ^ (n + 1)) q n)
    (q := (X : 𝕜[X]) ^ n)
  rw [natDegree_X_pow] at e3
  omega

lemma natDegree_oth_le (n : ℕ) (q : 𝕜) {j : ℕ} (hj : j ∈ range (n + 1)) :
    (Oth n q j).natDegree ≤ 4 * n := by
  unfold Oth
  refine (natDegree_prod_le _ _).trans ?_
  calc ∑ j' ∈ (range (n + 1)).erase j, (Lin q j' ^ 4).natDegree
        ≤ ∑ _j' ∈ (range (n + 1)).erase j, 4 :=
        sum_le_sum fun j' _ => natDegree_pow_le.trans (by have := natDegree_lin_le q j'; omega)
    _ = 4 * n := by rw [sum_const, card_erase_of_mem hj, card_range, smul_eq_mul, Nat.add_sub_cancel, mul_comm]

lemma natDegree_term_le (n : ℕ) (q : 𝕜) {j s : ℕ} (hj : j ∈ range (n + 1)) (hs : s ∈ Icc 1 4) :
    (C (cc n q s j) * (Lin q j ^ (4 - s) * Oth n q j)).natDegree ≤ 4 * n + 3 := by
  have hs1 : 1 ≤ s := (mem_Icc.mp hs).1
  have hO := natDegree_oth_le n q hj
  have hL : (Lin q j ^ (4 - s)).natDegree ≤ 4 - s :=
    natDegree_pow_le.trans ((Nat.mul_le_mul_left _ (natDegree_lin_le q j)).trans (mul_one _).le)
  have e1 := natDegree_C_mul_le (cc n q s j) (Lin q j ^ (4 - s) * Oth n q j)
  have e2 := natDegree_mul_le (p := Lin q j ^ (4 - s)) (q := Oth n q j)
  omega

lemma natDegree_hpoly_le (n : ℕ) (q : 𝕜) : (Hpoly n q).natDegree ≤ 4 * n + 3 := by
  unfold Hpoly
  refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · have := natDegree_npoly_le n q; omega
  · refine natDegree_sum_le_of_forall_le _ _ fun j hj => ?_
    exact natDegree_sum_le_of_forall_le _ _ fun s hs => natDegree_term_le n q hj hs

lemma natDegree_dpoly {q : 𝕜} (hq : q ≠ 0) (n : ℕ) : (Dpoly n q).natDegree = 4 * (n + 1) := by
  unfold Dpoly
  rw [natDegree_prod _ _ (fun j _ => pow_ne_zero _ (lin_ne_zero hq j))]
  simp only [natDegree_pow, natDegree_lin hq, sum_const, card_range, smul_eq_mul]
  ring

/-! ### Evaluation -/

lemma eval_qPochPoly (y q T : 𝕜) (m : ℕ) : (qPochPoly y q m).eval T = qPoch (y * T) q m := by
  simp only [qPochPoly, qPoch, eval_prod, eval_sub, eval_one, eval_mul, eval_C, eval_X]
  exact prod_congr rfl fun i _ => by ring

lemma eval_npoly (n : ℕ) (q T : 𝕜) : (Npoly n q).eval T =
    qPoch q q n ^ 2 * qPoch ((q ^ n)⁻¹ * T) q n * qPoch (q ^ (n + 1) * T) q n * T ^ n := by
  simp only [Npoly, eval_mul, eval_C, eval_qPochPoly, eval_pow, eval_X]

lemma eval_lin (q T : 𝕜) (j : ℕ) : (Lin q j).eval T = 1 - q ^ j * T := by
  simp only [Lin, eval_sub, eval_one, eval_mul, eval_C, eval_X]

end

end QZeta3.PartialFrac
