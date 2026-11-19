import QZeta3.Statements

/-!
# Assembly (PROOF_T1 §7)

`irrational_sub_inv_mul_zetaq3_of` derives `Irrational ((q − q⁻¹) ζ_q(3))` from the frozen
ingredients, for every real `q` with `0 < |q| < 1` and `q + q⁻¹ = s ∈ ℤ`.

`θ = q − q⁻¹` plays the role of `√d` (PROOF_T1 Remark 2): `θ² = s² − 4 =: D`, and the conjugation
`σ : q ↦ q⁻¹` sends `θ` to `−θ`.  If `θ ζ = a/b`, then `ζ = aθ/(bD)`, and for the integer
polynomial `Y = bD·X^{c₃}L₀ + a(2X − s)X^{c₀}L₃` (from `Integrality`):
* `Y(q) = q^c d_n(q)⁴ bD S_n` (by `Expansion`),
* `Y(q⁻¹) = −q^{−c−n} d_n(q⁻¹)⁴ bD S_n` (by `Recip`; note `2q⁻¹ − s = −θ`).
`Y(q) Y(q⁻¹)` is an integer (`norm_int`), nonzero (`SizeBound`, `dn_ne_zero`), so its square is
`≥ 1`; but by `SizeBound` and `CostBound` its square is `≤ K C^n |q|^{n² − 4n − 3} → 0`.
-/

open Polynomial Finset

namespace QZeta3

theorem pow_ne_one_of_abs_ne_one {τ : ℝ} (h : |τ| ≠ 1) : ∀ m : ℕ, 0 < m → τ ^ m ≠ 1 := by
  intro m hm hτ
  apply h
  have : |τ| ^ m = 1 := by rw [← abs_pow, hτ, abs_one]
  exact (pow_eq_one_iff_of_nonneg (abs_nonneg τ) hm.ne').mp this

theorem dn_ne_zero {x : ℝ} (hx : |x| ≠ 1) (n : ℕ) : dn n x ≠ 0 := by
  unfold dn
  refine Finset.prod_ne_zero_iff.mpr fun d hd => ?_
  have hd0 : 0 < d := by have := (mem_Icc.mp hd).1; omega
  intro h0
  have : NeZero d := ⟨hd0.ne'⟩
  have hroot : (cyclotomic d ℝ).IsRoot x := by
    rw [IsRoot, ← map_cyclotomic_int, eval_map]
    rw [aeval_def] at h0
    simpa using h0
  rw [isRoot_cyclotomic_iff] at hroot
  exact pow_ne_one_of_abs_ne_one hx d hd0 hroot.pow_eq_one

/-- Every `p(q)`, `p ∈ ℤ[X]`, is `u + v q` with `p(q⁻¹) = u + v q⁻¹` (`q + q⁻¹ = s ∈ ℤ`). -/
theorem eval_lin {q : ℝ} {s : ℤ} (hq0 : q ≠ 0) (hs : q + q⁻¹ = s) (p : ℤ[X]) :
    ∃ u v : ℤ, aeval q p = u + v * q ∧ aeval q⁻¹ p = u + v * q⁻¹ := by
  have hq2 : q * q = s * q - 1 := by
    have : q * (q + q⁻¹) = q * q + 1 := by field_simp
    rw [hs] at this; linarith
  have hqi2 : q⁻¹ * q⁻¹ = s * q⁻¹ - 1 := by
    have : q⁻¹ * (q + q⁻¹) = q⁻¹ * q⁻¹ + 1 := by field_simp; ring
    rw [hs] at this; linarith
  induction p using Polynomial.induction_on' with
  | add p r hp hr =>
    obtain ⟨u, v, h1, h2⟩ := hp
    obtain ⟨u', v', h1', h2'⟩ := hr
    exact ⟨u + u', v + v', by rw [map_add, h1, h1']; push_cast; ring,
      by rw [map_add, h2, h2']; push_cast; ring⟩
  | monomial k a =>
    induction k with
    | zero => exact ⟨a, 0, by simp, by simp⟩
    | succ k ih =>
      obtain ⟨u, v, h1, h2⟩ := ih
      refine ⟨-v, u + v * s, ?_, ?_⟩
      · have : aeval q (monomial (k + 1) a) = q * aeval q (monomial k a) := by
          simp [aeval_monomial, pow_succ]; ring
        rw [this, h1]; push_cast; linear_combination (v : ℝ) * hq2
      · have : aeval q⁻¹ (monomial (k + 1) a) = q⁻¹ * aeval q⁻¹ (monomial k a) := by
          simp [aeval_monomial, pow_succ]; ring
        rw [this, h2]; push_cast; linear_combination (v : ℝ) * hqi2

/-- `p(q) p(q⁻¹)` is an integer. -/
theorem norm_int {q : ℝ} {s : ℤ} (hq0 : q ≠ 0) (hs : q + q⁻¹ = s) (p : ℤ[X]) :
    ∃ z : ℤ, aeval q p * aeval q⁻¹ p = z := by
  obtain ⟨u, v, h1, h2⟩ := eval_lin hq0 hs p
  refine ⟨u ^ 2 + u * v * s + v ^ 2, ?_⟩
  rw [h1, h2]; push_cast
  have : q * q⁻¹ = 1 := mul_inv_cancel₀ hq0
  linear_combination (u * v : ℝ) * hs + (v : ℝ) ^ 2 * this

/-- The final estimate: `K C^n |q|^{n t} ≥ 1` fails for suitable large `n`. -/
theorem exists_large_n {κ K C : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1) (hK : 0 ≤ K) (N₀ : ℕ) :
    ∃ t : ℕ, N₀ ≤ t + 5 ∧ K * |C| ^ (t + 5) * κ ^ ((t + 5) * t) < 1 := by
  set C' := max |C| 1
  have hC' : 0 < C' := lt_of_lt_of_le one_pos (le_max_right _ _)
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (show 0 < 1 / (2 * C') by positivity) hκ1
  obtain ⟨p, hp⟩ := exists_pow_lt_of_lt_one (show 0 < 1 / (K + 1) by positivity)
    (show (1 / 2 : ℝ) < 1 by norm_num)
  refine ⟨N₀ + m + p, by omega, ?_⟩
  set t := N₀ + m + p
  have h1 : |C| ^ (t + 5) * κ ^ ((t + 5) * t) ≤ (C' * κ ^ t) ^ (t + 5) := by
    rw [mul_pow, ← pow_mul, mul_comm t (t + 5)]
    gcongr
    exact le_max_left _ _
  have h2 : C' * κ ^ t ≤ 1 / 2 := by
    have : κ ^ t ≤ κ ^ m := pow_le_pow_of_le_one hκ0.le hκ1.le (by omega)
    have h3 : C' * κ ^ m < C' * (1 / (2 * C')) := mul_lt_mul_of_pos_left hm hC'
    rw [show C' * (1 / (2 * C')) = 1 / 2 by field_simp] at h3
    nlinarith
  have h4 : (C' * κ ^ t) ^ (t + 5) ≤ (1 / 2 : ℝ) ^ p := by
    calc (C' * κ ^ t) ^ (t + 5) ≤ (1 / 2 : ℝ) ^ (t + 5) :=
          pow_le_pow_left₀ (by positivity) h2 _
      _ ≤ (1 / 2 : ℝ) ^ p := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have h5 : K * (|C| ^ (t + 5) * κ ^ ((t + 5) * t)) ≤ K * (1 / (K + 1)) :=
    mul_le_mul_of_nonneg_left (h1.trans (h4.trans hp.le)) hK
  have h6 : K * (1 / (K + 1)) < 1 := by
    rw [mul_one_div, div_lt_one (by linarith)]; linarith
  calc K * |C| ^ (t + 5) * κ ^ ((t + 5) * t) = K * (|C| ^ (t + 5) * κ ^ ((t + 5) * t)) := by ring
    _ < 1 := lt_of_le_of_lt h5 h6

theorem irrational_sub_inv_mul_zetaq3_of (hpf : PFIdentity) (hexp : PFIdentity → Expansion)
    (hrec : PFIdentity → Recip) (hint : Integrality) (hsize : SizeBound) (hcost : CostBound)
    {q : ℝ} {s : ℤ} (hq0 : q ≠ 0) (hq1 : |q| < 1) (hs : q + q⁻¹ = s) :
    Irrational ((q - q⁻¹) * zetaq3 q) := by
  have hexp' := hexp hpf
  rintro ⟨r, hr⟩
  have hκ0 : 0 < |q| := abs_pos.mpr hq0
  have hqabs : |q| ≠ 1 := ne_of_lt hq1
  have hqi0 : q⁻¹ ≠ 0 := inv_ne_zero hq0
  have hqiabs : |q⁻¹| ≠ 1 := by
    rw [abs_inv]; intro h; exact hqabs (inv_eq_one.mp h)
  set θ := q - q⁻¹ with hθ
  have hθ0 : θ ≠ 0 := by
    intro h
    have h1 : q * q = 1 := by
      have : q = q⁻¹ := sub_eq_zero.mp h
      calc q * q = q * q⁻¹ := by rw [← this]
        _ = 1 := mul_inv_cancel₀ hq0
    apply hqabs
    have : |q| * |q| = 1 := by rw [← abs_mul, h1, abs_one]
    nlinarith [abs_nonneg q]
  set D : ℤ := s ^ 2 - 4 with hDdef
  have hD : (D : ℝ) = θ ^ 2 := by
    have : θ ^ 2 = (q + q⁻¹) ^ 2 - 4 * (q * q⁻¹) := by rw [hθ]; ring
    rw [this, mul_inv_cancel₀ hq0, hs, hDdef]; push_cast; ring
  have hD0 : (D : ℝ) ≠ 0 := by rw [hD]; exact pow_ne_zero 2 hθ0
  set a : ℤ := r.num
  set b : ℕ := r.den
  have hb : (b : ℝ) ≠ 0 := by exact_mod_cast r.den_nz
  have hra : (r : ℝ) = a / b := by rw [Rat.cast_def]
  have hθs : 2 * q - s = θ := by rw [← hs, hθ]; ring
  have hθs' : 2 * q⁻¹ - s = -θ := by rw [← hs, hθ]; ring
  clear_value θ D
  have hζ : zetaq3 q = a * θ / (b * D) := by
    have h1 : zetaq3 q = (a / b) / θ := by
      rw [← hra, hr]; field_simp
    rw [h1, hD]; field_simp
  obtain ⟨CS, N₀, hS⟩ := hsize q hq0 hq1
  obtain ⟨Cc, hC⟩ := hcost q hq0 hq1
  set K : ℝ := ((b : ℝ) * D) ^ 4 * CS ^ 4 with hK
  obtain ⟨t, htN, ht⟩ := exists_large_n hκ0 hq1 (by positivity : 0 ≤ K) (max N₀ 1) (C := Cc)
  set n := t + 5 with hn
  have hn1 : 1 ≤ n := by omega
  clear_value n
  obtain ⟨hSne, hSle⟩ := hS n (le_trans (le_max_left _ _) htN)
  obtain ⟨⟨L0, c0, h0⟩, ⟨L3, c3, h3⟩⟩ := hint n hn1
  obtain ⟨hr3, hr0⟩ := hrec hpf n hn1 q hq0 hqabs
  have hexpn := hexp' n hn1 q hq0 hq1
  set Y : ℤ[X] := C ((b : ℤ) * D) * X ^ c3 * L0 + C a * (C 2 * X - C s) * X ^ c0 * L3 with hY
  have hYq : aeval q Y = q ^ (c0 + c3) * dn n q ^ 4 * (b * D) * Sn n q := by
    have e0 := h0 q hq0 hqabs
    have e3 := h3 q hq0 hqabs
    simp only [hY, map_add, map_mul, map_sub, map_pow, aeval_C, aeval_X, ← e0, ← e3,
      algebraMap_int_eq, eq_intCast, map_natCast, map_intCast, map_ofNat]
    push_cast
    rw [hθs, hexpn, hζ, pow_add]
    field_simp
  have hYqi : aeval q⁻¹ Y = -((q ^ (c0 + c3))⁻¹ * (q ^ n)⁻¹ * dn n q⁻¹ ^ 4 * (b * D) * Sn n q) := by
    have e0 := h0 q⁻¹ hqi0 hqiabs
    have e3 := h3 q⁻¹ hqi0 hqiabs
    simp only [hY, map_add, map_mul, map_sub, map_pow, aeval_C, aeval_X, ← e0, ← e3,
      algebraMap_int_eq, eq_intCast, map_natCast, map_intCast, map_ofNat]
    push_cast
    rw [hθs', hr0, hr3, hexpn, hζ, pow_add, inv_pow, inv_pow]
    field_simp
    ring
  obtain ⟨z, hz⟩ := norm_int hq0 hs Y
  have hdn := dn_ne_zero hqabs n
  have hdni := dn_ne_zero hqiabs n
  have hzval : (z : ℝ) = -((q ^ n)⁻¹ * (dn n q * dn n q⁻¹) ^ 4 * ((b : ℝ) * D) ^ 2 * Sn n q ^ 2) := by
    rw [← hz, hYq, hYqi]
    field_simp
  have hz0 : z ≠ 0 := by
    intro h0
    have : (z : ℝ) = 0 := by exact_mod_cast h0
    rw [hzval] at this
    have : (q ^ n)⁻¹ * (dn n q * dn n q⁻¹) ^ 4 * ((b : ℝ) * D) ^ 2 * Sn n q ^ 2 ≠ 0 := by
      have := mul_ne_zero hb hD0
      positivity
    simp_all
  have hz1 : (1 : ℝ) ≤ (z : ℝ) ^ 2 := by
    have : (1 : ℤ) ≤ z ^ 2 := by
      have := Int.one_le_abs hz0
      nlinarith [sq_abs z]
    exact_mod_cast this
  -- squared size: z² |q|^{2n} = (d d')^8 (bD)^4 S^4
  set κ := |q| with hκ
  have hz2 : (z : ℝ) ^ 2 * κ ^ (2 * n) = |dn n q * dn n q⁻¹| ^ 8 * ((b : ℝ) * D) ^ 4 * |Sn n q| ^ 4 := by
    rw [hzval, hκ]
    have hqn : (q ^ n) ≠ 0 := pow_ne_zero _ hq0
    have e1 : |dn n q * dn n q⁻¹| ^ 8 = (dn n q * dn n q⁻¹) ^ 8 := by
      rw [show (8 : ℕ) = 2 * 4 by rfl, pow_mul, sq_abs, ← pow_mul]
    have e2 : |Sn n q| ^ 4 = Sn n q ^ 4 := by
      rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, sq_abs, ← pow_mul]
    have e3 : |q| ^ (2 * n) = (q ^ n) ^ 2 := by
      rw [pow_mul', ← abs_pow, sq_abs]
    rw [e1, e2, e3]
    field_simp
  have hCn := hC n hn1
  have hS4 : |Sn n q| ^ 4 ≤ (CS * κ ^ (n * (n + 1))) ^ 4 :=
    pow_le_pow_left₀ (abs_nonneg _) hSle 4
  have hκ1 : κ < 1 := hq1
  -- combine: z² κ^{2n} κ^{3(n+1)²} ≤ K |Cc|^n κ^{4n(n+1)}
  have hmain : κ ^ (2 * n) * κ ^ (3 * (n + 1) ^ 2) ≤
      K * |Cc| ^ n * κ ^ (4 * (n * (n + 1))) := by
    have hA : κ ^ (2 * n) ≤ (z : ℝ) ^ 2 * κ ^ (2 * n) := by
      have := pow_pos hκ0 (2 * n); nlinarith
    have hB : |dn n q * dn n q⁻¹| ^ 8 * κ ^ (3 * (n + 1) ^ 2) ≤ |Cc| ^ n := by
      have hinv : (κ⁻¹) ^ (3 * (n + 1) ^ 2) * κ ^ (3 * (n + 1) ^ 2) = 1 := by
        rw [← mul_pow, inv_mul_cancel₀ hκ0.ne', one_pow]
      have hCc : Cc ^ n ≤ |Cc| ^ n := by
        calc Cc ^ n ≤ |Cc ^ n| := le_abs_self _
          _ = |Cc| ^ n := abs_pow _ _
      calc |dn n q * dn n q⁻¹| ^ 8 * κ ^ (3 * (n + 1) ^ 2)
          ≤ Cc ^ n * (κ⁻¹) ^ (3 * (n + 1) ^ 2) * κ ^ (3 * (n + 1) ^ 2) := by
            gcongr
        _ = Cc ^ n := by rw [mul_assoc, hinv, mul_one]
        _ ≤ |Cc| ^ n := hCc
    have hpos3 : 0 ≤ κ ^ (3 * (n + 1) ^ 2) := by positivity
    calc κ ^ (2 * n) * κ ^ (3 * (n + 1) ^ 2) ≤ (z : ℝ) ^ 2 * κ ^ (2 * n) * κ ^ (3 * (n + 1) ^ 2) :=
          mul_le_mul_of_nonneg_right hA hpos3
      _ = (|dn n q * dn n q⁻¹| ^ 8 * κ ^ (3 * (n + 1) ^ 2)) * (((b : ℝ) * D) ^ 4 * |Sn n q| ^ 4) := by
          rw [hz2]; ring
      _ ≤ |Cc| ^ n * (((b : ℝ) * D) ^ 4 * (CS * κ ^ (n * (n + 1))) ^ 4) := by
          gcongr
      _ = K * |Cc| ^ n * κ ^ (4 * (n * (n + 1))) := by rw [hK, mul_pow CS, ← pow_mul]; ring
  -- exponent bookkeeping: 4n(n+1) = 2n + 3(n+1)² + n t + (t + 2) with n = t + 5
  have hexp_eq : 4 * (n * (n + 1)) = (2 * n + 3 * (n + 1) ^ 2) + (n * t + (t + 2)) := by
    rw [hn]; ring
  rw [hexp_eq, pow_add κ, pow_add κ, pow_add κ] at hmain
  have hpos : 0 < κ ^ (2 * n) * κ ^ (3 * (n + 1) ^ 2) := by positivity
  have hle1 : κ ^ (t + 2) ≤ 1 := pow_le_one₀ hκ0.le hκ1.le
  have hfin : 1 ≤ K * |Cc| ^ n * κ ^ (n * t) := by
    have hK0 : 0 ≤ K * |Cc| ^ n := by positivity
    have h1 : κ ^ (2 * n) * κ ^ (3 * (n + 1) ^ 2) ≤
        κ ^ (2 * n) * κ ^ (3 * (n + 1) ^ 2) * (K * |Cc| ^ n * κ ^ (n * t)) := by
      calc κ ^ (2 * n) * κ ^ (3 * (n + 1) ^ 2) ≤
          K * |Cc| ^ n * (κ ^ (2 * n) * κ ^ (3 * (n + 1) ^ 2) * (κ ^ (n * t) * κ ^ (t + 2))) := hmain
        _ ≤ K * |Cc| ^ n * (κ ^ (2 * n) * κ ^ (3 * (n + 1) ^ 2) * (κ ^ (n * t) * 1)) := by
          gcongr
        _ = κ ^ (2 * n) * κ ^ (3 * (n + 1) ^ 2) * (K * |Cc| ^ n * κ ^ (n * t)) := by ring
    by_contra hlt
    push Not at hlt
    have := mul_lt_mul_of_pos_left hlt hpos
    linarith
  have : K * |Cc| ^ n * κ ^ (n * t) < 1 := ht
  linarith

end QZeta3
