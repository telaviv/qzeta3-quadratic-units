import QZeta3.PartialFrac.Basic

/-!
# Partial fractions (2.1): `PFIdentity`

PROOF_T1 §2, (2.1). Put `H = N − Σ_{j,s} c_{s,j} (1 − q^j T)^{4−s} ∏_{j' ≠ j} (1 − q^{j'} T)⁴`.
* `hcomp_dvd`: `u⁴ ∣ H(q^{−j}(1 − u))`, because `N(T(u)) = Gser · Dother` in `𝕜⟦u⟧` and
  `c_{s,j} = [u^{4−s}] Gser`.
* `hpoly_eq_zero`: so `(1 − q^j T)⁴ ∣ H` for every `j`; these are pairwise coprime, so `D ∣ H`,
  and `deg H < deg D` gives `H = 0`.
* `pf_generic`: evaluate at `T` and divide by `D(T)`.
-/

open Polynomial Finset

namespace QZeta3.PartialFrac

variable {𝕜 : Type*} [Field 𝕜]

lemma dother_const_ne {n : ℕ} {q : 𝕜} (hq : q ≠ 0) (hinj : ∀ i k : ℕ, q ^ i = q ^ k → i = k)
    (j : ℕ) : PowerSeries.constantCoeff (Dother n q j : PowerSeries 𝕜) ≠ 0 := by
  rw [Polynomial.constantCoeff_coe, coeff_zero_eq_eval_zero]
  simp only [Dother, Tsub, eval_prod, eval_pow, eval_sub, eval_one, eval_mul, eval_C, eval_X,
    sub_zero, mul_one]
  rw [prod_ne_zero_iff]
  intro j' hj'
  apply pow_ne_zero
  rw [sub_ne_zero]
  intro h
  have : q ^ j' = q ^ j := (mul_inv_eq_one₀ (pow_ne_zero _ hq)).mp h.symm
  exact (ne_of_mem_erase hj') (hinj j' j this)

lemma ncomp_eq (n : ℕ) {q : 𝕜} (hq : q ≠ 0) (hinj : ∀ i k : ℕ, q ^ i = q ^ k → i = k) (j : ℕ) :
    ((Npoly n q).comp (Tsub q j) : PowerSeries 𝕜) = Gser n q j * (Dother n q j : PowerSeries 𝕜) := by
  rw [Gser, mul_assoc, PowerSeries.inv_mul_cancel _ (dother_const_ne hq hinj j), mul_one]

lemma gser_sub_qpoly_dvd (n : ℕ) (q : 𝕜) (j : ℕ) :
    (PowerSeries.X : PowerSeries 𝕜) ^ 4 ∣ Gser n q j - (Qpoly n q j : PowerSeries 𝕜) := by
  rw [PowerSeries.X_pow_dvd_iff]
  intro m hm
  rw [map_sub, Polynomial.coeff_coe, Qpoly, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [show (Icc 1 4 : Finset ℕ) = {1, 2, 3, 4} by decide]
  interval_cases m <;> simp [cc]

lemma hcomp_dvd (n : ℕ) {q : 𝕜} (hq : q ≠ 0) (hinj : ∀ i k : ℕ, q ^ i = q ^ k → i = k)
    {j : ℕ} (hjr : j ∈ range (n + 1)) : X ^ 4 ∣ (Hpoly n q).comp (Tsub q j) := by
  have hj_term : ∑ s ∈ Icc 1 4, C (cc n q s j) *
      ((Lin q j ^ (4 - s)).comp (Tsub q j) * (Oth n q j).comp (Tsub q j)) =
      Qpoly n q j * Dother n q j := by
    rw [Qpoly, sum_mul]
    refine sum_congr rfl fun s _ => ?_
    rw [pow_comp, lin_comp_tsub hq, oth_comp_tsub, mul_assoc]
  have hsplit : (Hpoly n q).comp (Tsub q j) =
      ((Npoly n q).comp (Tsub q j) - Qpoly n q j * Dother n q j) -
      ∑ j2 ∈ (range (n + 1)).erase j, ∑ s ∈ Icc 1 4,
        C (cc n q s j2) * ((Lin q j2 ^ (4 - s)).comp (Tsub q j) * (Oth n q j2).comp (Tsub q j)) := by
    simp only [Hpoly, sub_comp, Polynomial.sum_comp, mul_comp, C_comp]
    rw [← add_sum_erase _ _ hjr, hj_term]
    ring
  rw [hsplit]
  refine dvd_sub ?_ ?_
  · rw [X_pow_dvd_iff]
    intro d hd
    have hPS : (((Npoly n q).comp (Tsub q j) - Qpoly n q j * Dother n q j : 𝕜[X]) : PowerSeries 𝕜)
        = (Gser n q j - (Qpoly n q j : PowerSeries 𝕜)) * (Dother n q j : PowerSeries 𝕜) := by
      rw [Polynomial.coe_sub, Polynomial.coe_mul, ncomp_eq n hq hinj j, sub_mul]
    have h1 : (PowerSeries.X : PowerSeries 𝕜) ^ 4 ∣
        (((Npoly n q).comp (Tsub q j) - Qpoly n q j * Dother n q j : 𝕜[X]) : PowerSeries 𝕜) := by
      rw [hPS]; exact dvd_mul_of_dvd_left (gser_sub_qpoly_dvd n q j) _
    rw [← Polynomial.coeff_coe]
    exact PowerSeries.X_pow_dvd_iff.mp h1 d hd
  · refine dvd_sum fun j2 hj2 => dvd_sum fun s _ => ?_
    refine Dvd.dvd.mul_left (Dvd.dvd.mul_left ?_ _) _
    have hjmem : j ∈ (range (n + 1)).erase j2 := mem_erase.mpr ⟨(ne_of_mem_erase hj2).symm, hjr⟩
    obtain ⟨K, hK⟩ := dvd_prod_of_mem (fun j' => Lin q j' ^ 4) hjmem
    have hK' : Oth n q j2 = Lin q j ^ 4 * K := by rw [Oth]; exact hK
    rw [hK', mul_comp, pow_comp, lin_comp_tsub hq]
    exact dvd_mul_right _ _

lemma hpoly_eq_zero (n : ℕ) {q : 𝕜} (hq : q ≠ 0) (hinj : ∀ i k : ℕ, q ^ i = q ^ k → i = k) :
    Hpoly n q = 0 := by
  have hdvd : Dpoly n q ∣ Hpoly n q := by
    unfold Dpoly
    apply Finset.prod_dvd_of_coprime
    · intro i _ k _ hik
      exact lin_pow_coprime fun h => hik (hinj i k h)
    · intro j hj
      exact lin_pow_dvd_of_comp hq j (hcomp_dvd n hq hinj hj)
  apply eq_zero_of_dvd_of_natDegree_lt hdvd
  rw [natDegree_dpoly hq]
  have := natDegree_hpoly_le n q
  omega

/-- (2.1) over any field, for `q ≠ 0` not a root of unity. -/
theorem pf_generic {n : ℕ} {q : 𝕜} (hq : q ≠ 0) (hinj : ∀ i k : ℕ, q ^ i = q ^ k → i = k)
    (T : 𝕜) (hT : ∀ j ∈ range (n + 1), q ^ j * T ≠ 1) :
    Rfun n q T = ∑ j ∈ range (n + 1), ∑ s ∈ Icc 1 4, cc n q s j / (1 - q ^ j * T) ^ s := by
  have hN : Npoly n q = ∑ j ∈ range (n + 1), ∑ s ∈ Icc 1 4,
      C (cc n q s j) * (Lin q j ^ (4 - s) * Oth n q j) := sub_eq_zero.mp (hpoly_eq_zero n hq hinj)
  have hNT := congrArg (eval T) hN
  rw [eval_npoly] at hNT
  simp only [eval_finsetSum, eval_mul, eval_C, eval_pow, eval_lin, Oth, eval_prod] at hNT
  have hden : qPoch T q (n + 1) ^ 4 = ∏ j ∈ range (n + 1), (1 - q ^ j * T) ^ 4 := by
    rw [qPoch, ← prod_pow]; exact prod_congr rfl fun i _ => by ring
  have ha : ∀ j ∈ range (n + 1), (1 - q ^ j * T) ≠ 0 := fun j hj => sub_ne_zero.mpr (hT j hj).symm
  rw [Rfun, hNT, hden, sum_div]
  refine sum_congr rfl fun j hj => ?_
  rw [sum_div]
  refine sum_congr rfl fun s hs => ?_
  have hs4 : s ≤ 4 := (mem_Icc.mp hs).2
  have hO : ∏ j' ∈ (range (n + 1)).erase j, (1 - q ^ j' * T) ^ 4 ≠ 0 :=
    prod_ne_zero_iff.mpr fun j' hj' => pow_ne_zero _ (ha j' (mem_of_mem_erase hj'))
  rw [← mul_prod_erase _ _ hj, show (1 - q ^ j * T) ^ 4 = (1 - q ^ j * T) ^ s * (1 - q ^ j * T) ^ (4 - s)
    by rw [← pow_add, Nat.add_sub_cancel' hs4], mul_assoc ((1 - q ^ j * T) ^ s),
    mul_div_mul_right _ _ (mul_ne_zero (pow_ne_zero _ (ha j hj)) hO)]

/-- **(2.1)**, the partial-fraction decomposition of `R_n` with the coefficients `cc`. -/
theorem pfIdentity : PFIdentity := by
  intro n _ q hq hq1 T hT
  refine pf_generic hq ?_ T hT
  intro i k h
  have h' : |q| ^ i = |q| ^ k := by rw [← abs_pow, ← abs_pow, h]
  exact pow_right_injective₀ (abs_pos.mpr hq) hq1 h'

end QZeta3.PartialFrac
