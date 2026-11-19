import QZeta3.Reciprocity.Coeff

/-!
# Reciprocity (PROOF_T1 Lemma 5, with k = n)

`P3 n q⁻¹ = q^{−n} P3 n q` and `P0 n q⁻¹ = −q^{−n} P0 n q`.
-/

open Polynomial Finset

namespace QZeta3.Reciprocity

/-- `W_{s,n−j}(1/q) = −W_{s,j}(q) − n` (PROOF_T1, proof of Lemma 5). -/
lemma Wf_inv (n s j : ℕ) (hj : j ≤ n) (q : ℝ) :
    Wf n q⁻¹ s (n - j) = -Wf n q s j - n := by
  unfold Wf
  rw [Nat.sub_sub_self hj]
  simp only [inv_pow, inv_inv, sum_sub_distrib, sum_const, Nat.card_Icc, add_tsub_cancel_right,
    nsmul_eq_mul, mul_one]
  rw [Nat.cast_sub hj]
  ring

/-- `Σ_{s,j} c_{s,j} = R_n(0) = 0`, from the partial-fraction identity at `T = 0`. -/
lemma sum_cc_eq_zero (hpf : PFIdentity) {n : ℕ} (hn : 1 ≤ n) {q : ℝ} (hq : q ≠ 0)
    (hq1 : |q| ≠ 1) : ∑ j ∈ range (n + 1), ∑ s ∈ Icc 1 4, cc n q s j = 0 := by
  have h := hpf n hn q hq hq1 0 (fun j _ => by simp)
  have h0 : Rfun n q 0 = 0 := by
    unfold Rfun
    rw [zero_pow (by omega : n ≠ 0)]
    simp
  rw [h0] at h
  simpa using h.symm

/-- PROOF_T1 Lemma 5 (reciprocity), `k = n`. -/
theorem recip (hpf : PFIdentity) : Recip := by
  intro n hn q hq hq1
  have hsum := sum_cc_eq_zero hpf hn hq hq1
  have hcc : ∀ s, ∀ j ∈ range (n + 1), cc n q⁻¹ s j = (q ^ n)⁻¹ * cc n q s (n - j) :=
    fun s j hj => cc_inv hq (by simp only [mem_range] at hj; omega) s
  constructor
  · unfold P3
    calc ∑ j ∈ range (n + 1), (cc n q⁻¹ 3 j + 2 * cc n q⁻¹ 4 j)
        = ∑ j ∈ range (n + 1),
            (q ^ n)⁻¹ * (cc n q 3 (n + 1 - 1 - j) + 2 * cc n q 4 (n + 1 - 1 - j)) := by
          refine sum_congr rfl fun j hj => ?_
          rw [hcc 3 j hj, hcc 4 j hj, Nat.add_sub_cancel]
          ring
      _ = (q ^ n)⁻¹ * ∑ j ∈ range (n + 1), (cc n q 3 j + 2 * cc n q 4 j) := by
          rw [← mul_sum, sum_range_reflect (fun j => cc n q 3 j + 2 * cc n q 4 j) (n + 1)]
  · calc P0 n q⁻¹
        = -∑ j ∈ range (n + 1), ∑ s ∈ Icc 1 4,
            cc n q⁻¹ s (n + 1 - 1 - j) * Wf n q⁻¹ s (n + 1 - 1 - j) := by
          unfold P0
          rw [sum_range_reflect (fun j => ∑ s ∈ Icc 1 4, cc n q⁻¹ s j * Wf n q⁻¹ s j) (n + 1)]
      _ = -∑ j ∈ range (n + 1), ∑ s ∈ Icc 1 4,
            ((q ^ n)⁻¹ * cc n q s j) * (-Wf n q s j - n) := by
          congr 1
          refine sum_congr rfl fun j hj => sum_congr rfl fun s _ => ?_
          have hj' : j ≤ n := by simp only [mem_range] at hj; omega
          rw [Nat.add_sub_cancel, hcc s (n - j) (by simp only [mem_range]; omega),
            Nat.sub_sub_self hj', Wf_inv n s j hj']
      _ = -∑ j ∈ range (n + 1), ∑ s ∈ Icc 1 4,
            (-((q ^ n)⁻¹ * (cc n q s j * Wf n q s j)) - (q ^ n)⁻¹ * n * cc n q s j) := by
          congr 1
          exact sum_congr rfl fun j _ => sum_congr rfl fun s _ => by ring
      _ = -((q ^ n)⁻¹ * P0 n q) := by
          simp only [sum_sub_distrib, sum_neg_distrib, ← mul_sum, hsum, P0]
          ring

end QZeta3.Reciprocity
