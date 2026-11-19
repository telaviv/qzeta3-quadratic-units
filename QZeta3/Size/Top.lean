import QZeta3.Size.Poch
import QZeta3.Size.Symm

/-!
# Size: Lemma 6 (size and non-vanishing), A = 4, r = 1, e = n

PROOF_T1 §5. With `a_k = R_n(q^{k+1})` and Lemma 1,
`S_n = Σ_k (1 - q^{2n} q^{4(k+1)}) a_k`; `a_k = 0` for `k < n`, `|a_k| ≤ e^{8K} κ^{(k+1)n}`,
and `|a_n| ≥ e^{-8K} κ^{n(n+1)}`. The `k = n` term dominates the geometric tail for large `n`.
-/

open Finset Real

namespace QZeta3.Size

/-- `a_k = R_n(q^{k+1})`. -/
noncomputable def aT (n : ℕ) (q : ℝ) (k : ℕ) : ℝ := Rfun n q (q ^ (k + 1))

/-- `w_k = 1 - q^{2n} (q^{k+1})^4`. -/
noncomputable def wT (n : ℕ) (q : ℝ) (k : ℕ) : ℝ := 1 - q ^ (2 * n) * (q ^ (k + 1)) ^ 4

lemma aT_le {q : ℝ} (hq0 : q ≠ 0) (hq : |q| < 1) (n k : ℕ) :
    |aT n q k| ≤ exp (8 * Kc q) * |q| ^ ((k + 1) * n) := by
  unfold aT
  rcases lt_or_ge k n with h | h
  · rw [Rfun_pow_eq_zero hq0 (by omega) (by omega), abs_zero]; positivity
  · exact (Rfun_pow_bounds hq0 hq (by omega)).2

lemma aT_eq_zero {q : ℝ} (hq0 : q ≠ 0) {n k : ℕ} (hk : k < n) : aT n q k = 0 :=
  Rfun_pow_eq_zero hq0 (by omega) (by omega)

/-- Lemma 1 at `T = q^{k+1}`. -/
lemma Rfun_neg {q : ℝ} (hq0 : q ≠ 0) (n k : ℕ) :
    Rfun n q (q ^ (n + k + 1))⁻¹ = q ^ (2 * n) * (q ^ (k + 1)) ^ 4 * aT n q k := by
  have h : n + k + 1 = n + (k + 1) := by omega
  rw [h, pow_add, mul_inv, Rfun_symm hq0 (pow_ne_zero _ hq0) n, aT]

theorem sizeBound : SizeBound := by
  intro q hq0 hq
  have hκ0 : 0 < |q| := abs_pos.mpr hq0
  have h1κ : 0 < 1 - |q| := by linarith
  have hK : 0 ≤ Kc q := by unfold Kc; positivity
  have hEpos : 0 < exp (8 * Kc q) := exp_pos _
  have hepos : 0 < exp (-(8 * Kc q)) := exp_pos _
  have hE1 : 1 ≤ exp (8 * Kc q) := one_le_exp (by linarith)
  have he1 : exp (-(8 * Kc q)) ≤ 1 := exp_le_one_iff.mpr (by linarith)
  -- `δ = (1 - κ) e^{-8K} / (4 e^{8K})`
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one
    (by positivity : 0 < (1 - |q|) * exp (-(8 * Kc q)) / (4 * exp (8 * Kc q))) hq
  refine ⟨3 * exp (8 * Kc q), max N 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_of_max_le_right hn
  have hnN : N ≤ n := le_of_max_le_left hn
  have hρδ : |q| ^ n < (1 - |q|) * exp (-(8 * Kc q)) / (4 * exp (8 * Kc q)) :=
    lt_of_le_of_lt (pow_le_pow_of_le_one hκ0.le hq.le hnN) hN
  have hρ4 : |q| ^ n ≤ 1 / 4 := by
    refine hρδ.le.trans ?_
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [mul_le_mul_of_nonneg_right (by linarith : 1 - |q| ≤ 1) hepos.le]
  have hρ0 : 0 ≤ |q| ^ n := by positivity
  have hρ1 : |q| ^ n < 1 := by linarith
  have hX0 : 0 < |q| ^ (n * (n + 1)) := by positivity
  set E := exp (8 * Kc q) with hE
  set e := exp (-(8 * Kc q)) with he
  -- the weights
  have hsmall : ∀ k : ℕ, |q ^ (2 * n) * (q ^ (k + 1)) ^ 4| ≤ |q| := by
    intro k
    rw [abs_mul, abs_pow, abs_pow, abs_pow, ← pow_mul, ← pow_add]
    exact pow_le_of_le_one hκ0.le hq.le (by omega)
  have hw2 : ∀ k, |wT n q k| ≤ 2 := by
    intro k
    calc |wT n q k| ≤ |1| + |q ^ (2 * n) * (q ^ (k + 1)) ^ 4| := abs_sub _ _
      _ ≤ 2 := by rw [abs_one]; linarith [hsmall k]
  have hw1 : ∀ k, 1 - |q| ≤ |wT n q k| := by
    intro k
    calc 1 - |q| ≤ |1| - |q ^ (2 * n) * (q ^ (k + 1)) ^ 4| := by
          rw [abs_one]; linarith [hsmall k]
      _ ≤ |wT n q k| := abs_sub_abs_le_abs_sub _ _
  -- the terms `a_k`
  have ha_le : ∀ k, |aT n q k| ≤ E * |q| ^ n * (|q| ^ n) ^ k := by
    intro k
    have h := aT_le hq0 hq n k
    have e2 : |q| ^ ((k + 1) * n) = |q| ^ n * (|q| ^ n) ^ k := by ring
    rw [e2, ← mul_assoc] at h; exact h
  have hgeo := summable_geometric_of_lt_one hρ0 hρ1
  have hsa : Summable (aT n q) :=
    Summable.of_norm_bounded (hgeo.mul_left (E * |q| ^ n)) (fun k => by
      rw [Real.norm_eq_abs]; exact ha_le k)
  have hsb : Summable (fun k => q ^ (2 * n) * (q ^ (k + 1)) ^ 4 * aT n q k) :=
    Summable.of_norm_bounded (hgeo.mul_left (E * |q| ^ n)) (fun k => by
      rw [Real.norm_eq_abs, abs_mul]
      calc _ ≤ 1 * |aT n q k| :=
            mul_le_mul_of_nonneg_right ((hsmall k).trans hq.le) (abs_nonneg _)
        _ ≤ _ := by rw [one_mul]; exact ha_le k)
  have hSdef : Sn n q = ∑' k, aT n q k - ∑' k, Rfun n q (q ^ (n + k + 1))⁻¹ := rfl
  have hb : (fun k : ℕ => Rfun n q (q ^ (n + k + 1))⁻¹) =
      fun k => q ^ (2 * n) * (q ^ (k + 1)) ^ 4 * aT n q k := by
    funext k; exact Rfun_neg hq0 n k
  have hS : Sn n q = ∑' k, wT n q k * aT n q k := by
    rw [hSdef, hb, ← hsa.tsum_sub hsb]
    congr 1; funext k; unfold wT; ring
  -- the terms `c_k = w_k a_k`
  have hc_le : ∀ k, |wT n q k * aT n q k| ≤ 2 * (E * |q| ^ n * (|q| ^ n) ^ k) := by
    intro k; rw [abs_mul]; exact mul_le_mul (hw2 k) (ha_le k) (abs_nonneg _) (by norm_num)
  have hsc : Summable (fun k => wT n q k * aT n q k) :=
    Summable.of_norm_bounded ((hgeo.mul_left (E * |q| ^ n)).mul_left 2) (fun k => by
      rw [Real.norm_eq_abs]; exact hc_le k)
  have hshift : ∑' k, wT n q k * aT n q k = ∑' k, wT n q (k + n) * aT n q (k + n) := by
    rw [← hsc.sum_add_tsum_nat_add n, sum_eq_zero (fun k hk => by
      rw [aT_eq_zero hq0 (by simpa using hk), mul_zero]), zero_add]
  have hsd : Summable (fun k => wT n q (k + n) * aT n q (k + n)) :=
    (summable_nat_add_iff n).mpr hsc
  have hsplit : ∑' k, wT n q (k + n) * aT n q (k + n) =
      wT n q n * aT n q n + ∑' k, wT n q (k + 1 + n) * aT n q (k + 1 + n) := by
    rw [hsd.tsum_eq_zero_add]; simp only [zero_add]
  -- the tail
  have htail : |∑' k, wT n q (k + 1 + n) * aT n q (k + 1 + n)| ≤
      2 * E * |q| ^ (n * (n + 1)) * |q| ^ n * (1 - |q| ^ n)⁻¹ := by
    rw [← Real.norm_eq_abs]
    refine tsum_of_norm_bounded ((hasSum_geometric_of_lt_one hρ0 hρ1).mul_left
      (2 * E * |q| ^ (n * (n + 1)) * |q| ^ n)) (fun k => ?_)
    rw [Real.norm_eq_abs]
    calc _ ≤ 2 * (E * |q| ^ n * (|q| ^ n) ^ (k + 1 + n)) := hc_le _
      _ = 2 * E * |q| ^ (n * (n + 1)) * |q| ^ n * (|q| ^ n) ^ k := by ring
  have hr2 : |q| ^ n * (1 - |q| ^ n)⁻¹ ≤ 2 * |q| ^ n := by
    rw [← div_eq_mul_inv, div_le_iff₀ (by linarith)]; nlinarith
  have ht : |∑' k, wT n q (k + 1 + n) * aT n q (k + 1 + n)| ≤
      4 * E * |q| ^ (n * (n + 1)) * |q| ^ n := by
    refine htail.trans ?_
    have := mul_le_mul_of_nonneg_left hr2 (by positivity : 0 ≤ 2 * E * |q| ^ (n * (n + 1)))
    calc _ = 2 * E * |q| ^ (n * (n + 1)) * (|q| ^ n * (1 - |q| ^ n)⁻¹) := by ring
      _ ≤ _ := this
      _ = _ := by ring
  -- the main term `k = n`
  have hb_n := Rfun_pow_bounds hq0 hq (le_refl (n + 1))
  rw [mul_comm (n + 1) n] at hb_n
  have hcn_lo : (1 - |q|) * (e * |q| ^ (n * (n + 1))) ≤ |wT n q n * aT n q n| := by
    rw [abs_mul]; exact mul_le_mul (hw1 n) hb_n.1 (by positivity) (abs_nonneg _)
  have hcn_hi : |wT n q n * aT n q n| ≤ 2 * (E * |q| ^ (n * (n + 1))) := by
    rw [abs_mul]; exact mul_le_mul (hw2 n) hb_n.2 (abs_nonneg _) (by norm_num)
  have hδ4 : (1 - |q|) * e / (4 * E) * (4 * E) = (1 - |q|) * e := by
    field_simp
  rw [hS, hshift, hsplit]
  set t := ∑' k, wT n q (k + 1 + n) * aT n q (k + 1 + n)
  set c := wT n q n * aT n q n
  constructor
  · intro h0
    have hct : c = -t := by linarith
    have h1 : |c| ≤ 4 * E * |q| ^ (n * (n + 1)) * |q| ^ n := by rw [hct, abs_neg]; exact ht
    have h2 : 4 * E * |q| ^ (n * (n + 1)) * |q| ^ n <
        4 * E * |q| ^ (n * (n + 1)) * ((1 - |q|) * e / (4 * E)) :=
      mul_lt_mul_of_pos_left hρδ (by positivity)
    have h3 : 4 * E * |q| ^ (n * (n + 1)) * ((1 - |q|) * e / (4 * E)) =
        (1 - |q|) * (e * |q| ^ (n * (n + 1))) := by
      calc _ = |q| ^ (n * (n + 1)) * ((1 - |q|) * e / (4 * E) * (4 * E)) := by ring
        _ = _ := by rw [hδ4]; ring
    linarith
  · calc |c + t| ≤ |c| + |t| := abs_add_le _ _
      _ ≤ 2 * (E * |q| ^ (n * (n + 1))) + 4 * E * |q| ^ (n * (n + 1)) * |q| ^ n :=
          add_le_add hcn_hi ht
      _ ≤ 3 * E * |q| ^ (n * (n + 1)) := by
          have := mul_le_mul_of_nonneg_left hρ4 (by positivity : 0 ≤ 4 * E * |q| ^ (n * (n + 1)))
          nlinarith

end QZeta3.Size
