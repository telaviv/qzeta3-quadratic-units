import QZeta3.Denom.Gser

/-!
# Integrality (PROOF_T1 Lemma 3 and §7)

* `cc_laurent`: `d_n^{4−s} c_{s,j}` is `LaurentInt` (Lemma 3).
* `Wf_laurent`: `d_n^s W_{s,j}` is `LaurentInt` (§7, second bullet).
* `integrality`: `d_n⁴ P₀ = −Σ (d_n^{4−s} c_{s,j})(d_n^s W_{s,j})` and
  `d_n⁴ P₃ = Σ_j (d_n³ · d_n c_{3,j} + 2 d_n⁴ c_{4,j})` are `LaurentInt`.
-/

open Polynomial Finset

namespace QZeta3.Denom

theorem cc_laurent {n s j : ℕ} (hj : j ∈ range (n + 1)) :
    LaurentInt (fun x => dn n x ^ (4 - s) * cc n x s j) :=
  serInt_Gser hj (4 - s)

theorem Wf_laurent {n s j : ℕ} (hj : j ≤ n) : LaurentInt (fun x => dn n x ^ s * Wf n x s j) := by
  refine ((LaurentInt.sum (Icc 1 j)
    (f := fun m x => (dn n x * (1 - x ^ m)⁻¹) ^ s - dn n x ^ s) fun m hm => ?_).sub
    (LaurentInt.sum (Icc 1 (n - j))
      (f := fun m x => (dn n x * (1 - (x ^ m)⁻¹)⁻¹) ^ s) fun m hm => ?_)).congr fun x _ _ => ?_
  · obtain ⟨h1, h2⟩ := mem_Icc.1 hm
    exact ((dn_div n m h1 (h2.trans hj)).pow s).sub ((dn_laurent n).pow s)
  · obtain ⟨h1, h2⟩ := mem_Icc.1 hm
    exact (dn_div_inv n m h1 (by omega)).pow s
  · rw [Wf, mul_sub, mul_sum, mul_sum]
    congr 1
    · refine sum_congr rfl fun m _ => ?_
      rw [mul_pow, inv_pow]
      ring
    · refine sum_congr rfl fun m _ => ?_
      rw [mul_pow, inv_pow]

/-- **Lemma 3 and §7**: `d_n⁴ P₀` and `d_n⁴ P₃` are integer Laurent polynomials. -/
theorem integrality : Integrality := by
  intro n _
  constructor
  · refine (LaurentInt.sum (range (n + 1))
      (f := fun j x => ∑ s ∈ Icc 1 4, (dn n x ^ (4 - s) * cc n x s j) * (dn n x ^ s * Wf n x s j))
      fun j hj => LaurentInt.sum _ fun s _ =>
        (cc_laurent hj).mul (Wf_laurent (Nat.lt_succ_iff.1 (mem_range.1 hj)))).neg.congr
      fun x _ _ => ?_
    rw [P0, mul_neg, mul_sum]
    congr 1
    refine sum_congr rfl fun j _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun s hs => ?_
    have h4 : dn n x ^ 4 = dn n x ^ (4 - s) * dn n x ^ s := by
      rw [← pow_add]
      congr 1
      have := (mem_Icc.1 hs).2
      omega
    rw [h4]
    ring
  · refine (LaurentInt.sum (range (n + 1))
      (f := fun j x => dn n x ^ 3 * (dn n x ^ (4 - 3) * cc n x 3 j) +
        ((2 : ℤ) : ℝ) * (dn n x ^ 4 * (dn n x ^ (4 - 4) * cc n x 4 j)))
      fun j hj => (((dn_laurent n).pow 3).mul (cc_laurent (s := 3) hj)).add
        ((LaurentInt.intCast 2).mul (((dn_laurent n).pow 4).mul (cc_laurent (s := 4) hj)))).congr
      fun x _ _ => ?_
    rw [P3, mul_sum]
    refine sum_congr rfl fun j _ => ?_
    norm_num
    ring

end QZeta3.Denom
