import QZeta3.Expand.Analytic

/-!
# Lemma 4 (expansion), A = 4: `S_n = P₀ + P₃ ζ_q(3)`

PROOF_T1 §3. From the partial fractions (`PFIdentity`):
* `Σ_{s,j} c_{s,j} = R_n(0) = 0` (`sum_cc_zero`);
* `R(q^{k+1}) = Σ c_{s,j} fS s (q^{k+j+1})` (`Rfun_pos`) and
  `R(q^{−(n+k+1)}) = Σ c_{s,j} gS s (q^{k+(n−j)+1})` (`Rfun_neg`);
* summing over `k` (shifted geometric-type series) and subtracting gives
  `Σ c_{s,j} (F_s − G_s) + P₀`, and `F_s − G_s = 2 L + aS s · ζ_q(3)` (`Fsum_sub_Gsum`).
-/

open Finset

namespace QZeta3.Expand

/-- `F_s = Σ_{m ≥ 1} ((1 − q^m)^{−s} − 1)`. -/
noncomputable def Fsum (q : ℝ) (s : ℕ) : ℝ := ∑' m : ℕ, fS s (q ^ (m + 1))

/-- `G_s = Σ_{m ≥ 1} (1 − q^{−m})^{−s}`. -/
noncomputable def Gsum (q : ℝ) (s : ℕ) : ℝ := ∑' m : ℕ, gS s (q ^ (m + 1))

/-- `L = Σ_{m ≥ 1} q^m/(1 − q^m)`. -/
noncomputable def Lsum (q : ℝ) : ℝ := ∑' m : ℕ, lam (q ^ (m + 1))

lemma Rfun_zero {n : ℕ} (hn : 1 ≤ n) (q : ℝ) : Rfun n q 0 = 0 := by
  simp [Rfun, zero_pow (by omega : n ≠ 0)]

section Main

variable (hpf : PFIdentity) {n : ℕ} (hn : 1 ≤ n) {q : ℝ} (hq0 : q ≠ 0) (hq : |q| < 1)
include hpf hn hq0 hq

/-- `Σ_{s,j} c_{s,j} = R_n(0) = 0`. -/
lemma sum_cc_zero : ∑ j ∈ range (n + 1), ∑ s ∈ Icc 1 4, cc n q s j = 0 := by
  have h := hpf n hn q hq0 hq.ne 0 (by simp)
  rw [Rfun_zero hn q] at h
  simpa using h.symm

lemma Rfun_pos (k : ℕ) :
    Rfun n q (q ^ (k + 1)) =
      ∑ j ∈ range (n + 1), ∑ s ∈ Icc 1 4, cc n q s j * fS s (q ^ (k + j + 1)) := by
  have hT : ∀ j ∈ range (n + 1), q ^ j * q ^ (k + 1) ≠ 1 := by
    intro j _
    rw [← pow_add, show j + (k + 1) = (k + j) + 1 by ring]
    exact pow_succ_ne_one hq0 hq _
  rw [hpf n hn q hq0 hq.ne _ hT]
  have h0 := sum_cc_zero hpf hn hq0 hq
  calc _ = ∑ j ∈ range (n + 1), ∑ s ∈ Icc 1 4,
        (cc n q s j * fS s (q ^ (k + j + 1)) + cc n q s j) := by
        refine sum_congr rfl fun j _ => sum_congr rfl fun s _ => ?_
        rw [fS, ← pow_add, show j + (k + 1) = k + j + 1 by ring]
        ring
    _ = _ := by simp only [sum_add_distrib, h0, add_zero]

lemma Rfun_neg (k : ℕ) :
    Rfun n q (q ^ (n + k + 1))⁻¹ =
      ∑ j ∈ range (n + 1), ∑ s ∈ Icc 1 4, cc n q s j * gS s (q ^ (k + (n - j) + 1)) := by
  have key : ∀ j ∈ range (n + 1), q ^ j * (q ^ (n + k + 1))⁻¹ = (q ^ (k + (n - j) + 1))⁻¹ := by
    intro j hj
    have hj' : j ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hj)
    rw [show n + k + 1 = j + (k + (n - j) + 1) by omega, pow_add, mul_inv, ← mul_assoc,
      mul_inv_cancel₀ (pow_ne_zero _ hq0), one_mul]
  have hT : ∀ j ∈ range (n + 1), q ^ j * (q ^ (n + k + 1))⁻¹ ≠ 1 := by
    intro j hj h
    rw [key j hj] at h
    exact pow_succ_ne_one hq0 hq _ (inv_eq_one.mp h)
  rw [hpf n hn q hq0 hq.ne _ hT]
  refine sum_congr rfl fun j hj => sum_congr rfl fun s _ => ?_
  rw [key j hj, gS, div_eq_mul_inv]

lemma hasSum_pos : HasSum (fun k : ℕ => Rfun n q (q ^ (k + 1)))
    (∑ j ∈ range (n + 1), ∑ s ∈ Icc 1 4,
      cc n q s j * (Fsum q s - ∑ i ∈ range j, fS s (q ^ (i + 1)))) := by
  have hfun : (fun k : ℕ => Rfun n q (q ^ (k + 1))) = fun k =>
      ∑ j ∈ range (n + 1), ∑ s ∈ Icc 1 4, cc n q s j * fS s (q ^ (k + j + 1)) :=
    funext (Rfun_pos hpf hn hq0 hq)
  rw [hfun]
  exact hasSum_sum fun j _ => hasSum_sum fun s hs =>
    ((hasSum_nat_add_iff' (f := fun i : ℕ => fS s (q ^ (i + 1))) j).mpr
      (summable_fS hq0 hq hs).hasSum).mul_left (cc n q s j)

lemma hasSum_neg : HasSum (fun k : ℕ => Rfun n q (q ^ (n + k + 1))⁻¹)
    (∑ j ∈ range (n + 1), ∑ s ∈ Icc 1 4,
      cc n q s j * (Gsum q s - ∑ i ∈ range (n - j), gS s (q ^ (i + 1)))) := by
  have hfun : (fun k : ℕ => Rfun n q (q ^ (n + k + 1))⁻¹) = fun k =>
      ∑ j ∈ range (n + 1), ∑ s ∈ Icc 1 4, cc n q s j * gS s (q ^ (k + (n - j) + 1)) :=
    funext (Rfun_neg hpf hn hq0 hq)
  rw [hfun]
  exact hasSum_sum fun j _ => hasSum_sum fun s hs =>
    ((hasSum_nat_add_iff' (f := fun i : ℕ => gS s (q ^ (i + 1))) (n - j)).mpr
      (summable_gS hq0 hq (mem_Icc.mp hs).1).hasSum).mul_left (cc n q s j)

end Main

lemma Fsum_sub_Gsum {q : ℝ} (hq0 : q ≠ 0) (hq : |q| < 1) {s : ℕ} (hs : s ∈ Icc 1 4) :
    Fsum q s - Gsum q s = 2 * Lsum q + aS s * zetaq3 q := by
  have h1 : HasSum (fun m : ℕ => 2 * lam (q ^ (m + 1)) + aS s * zet (q ^ (m + 1)))
      (Fsum q s - Gsum q s) := by
    have := (summable_fS hq0 hq hs).hasSum.sub (summable_gS hq0 hq (mem_Icc.mp hs).1).hasSum
    rw [Fsum, Gsum]
    convert this using 1
    funext m
    exact (fS_sub_gS hs (pow_ne_zero _ hq0) (pow_succ_ne_one hq0 hq m)).symm
  exact h1.unique (((summable_lam hq0 hq).hasSum.mul_left 2).add
    ((hasSum_zet hq0 hq).mul_left (aS s)))

/-- **Lemma 4** (A = 4): `S_n(q) = P₀(q) + P₃(q) ζ_q(3)` for real `0 < |q| < 1`. -/
theorem expansion (hpf : PFIdentity) : Expansion := by
  intro n hn q hq0 hq
  have h0 := sum_cc_zero hpf hn hq0 hq
  rw [Sn, (hasSum_pos hpf hn hq0 hq).tsum_eq, (hasSum_neg hpf hn hq0 hq).tsum_eq]
  calc _ = ∑ j ∈ range (n + 1), ∑ s ∈ Icc 1 4,
        (cc n q s j * (2 * Lsum q + aS s * zetaq3 q) - cc n q s j * Wf n q s j) := by
        rw [← sum_sub_distrib]
        refine sum_congr rfl fun j _ => ?_
        rw [← sum_sub_distrib]
        refine sum_congr rfl fun s hs => ?_
        rw [← Fsum_sub_Gsum hq0 hq hs]
        simp only [Wf, sum_Icc_one, fS, gS]
        ring
    _ = ∑ j ∈ range (n + 1), (2 * Lsum q * ∑ s ∈ Icc 1 4, cc n q s j
          + zetaq3 q * (cc n q 3 j + 2 * cc n q 4 j)
          - ∑ s ∈ Icc 1 4, cc n q s j * Wf n q s j) := by
        refine sum_congr rfl fun j _ => ?_
        rw [sum_Icc14, sum_Icc14, sum_Icc14]
        norm_num [aS]
        ring
    _ = 2 * Lsum q * (∑ j ∈ range (n + 1), ∑ s ∈ Icc 1 4, cc n q s j)
          + zetaq3 q * P3 n q
          - ∑ j ∈ range (n + 1), ∑ s ∈ Icc 1 4, cc n q s j * Wf n q s j := by
        rw [sum_sub_distrib, sum_add_distrib, ← mul_sum, ← mul_sum, P3]
    _ = _ := by
        rw [h0, P0]
        ring

end QZeta3.Expand
