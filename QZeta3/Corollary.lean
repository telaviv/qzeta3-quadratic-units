import QZeta3.Defs

/-!
# The Lucas-sequence corollary: algebra (PROOF_T1 §0, proof of the Corollary)

For admissible `(a, E)` (`E = 1, a ≥ 1` or `E = −1, a ≥ 3`) put `Δ = a² + 4E`,
`ε = (a + √Δ)/2`, `ε̄ = (a − √Δ)/2` (so `ε + ε̄ = a`, `ε ε̄ = −E`), and `q = ε̄/ε`.
Then `q + q⁻¹ = −E a² − 2 ∈ ℤ`, `0 < |q| < 1`, `Δ (s² − 4) = (aΔ)²`, and termwise
`m² (U_{m+1}/U_m − ε) = √Δ · m² q^m/(1 − q^m)` (Binet: `√Δ U_m = ε^m − ε̄^m`,
`U_{m+1} − ε U_m = ε̄^m`).
-/

open Finset

namespace QZeta3

/-- Admissible parameters of a quadratic-unit Lucas sequence. -/
def Adm (a : ℕ) (E : ℤ) : Prop := (E = 1 ∧ 1 ≤ a) ∨ (E = -1 ∧ 3 ≤ a)

/-- The discriminant `Δ = a² + 4E`. -/
def discr (a : ℕ) (E : ℤ) : ℤ := (a : ℤ) ^ 2 + 4 * E

/-- The conjugate root `ε̄ = (a − √Δ)/2`. -/
noncomputable def epsBar (a : ℕ) (E : ℤ) : ℝ := (a - Real.sqrt ((a : ℝ) ^ 2 + 4 * E)) / 2

/-- `q = ε̄/ε`. -/
noncomputable def qU (a : ℕ) (E : ℤ) : ℝ := epsBar a E / epsU a E

variable {a : ℕ} {E : ℤ}

theorem E_sq (h : Adm a E) : E ^ 2 = 1 := by
  rcases h with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> norm_num

theorem discr_ge (h : Adm a E) : (5 : ℝ) ≤ (a : ℝ) ^ 2 + 4 * E := by
  rcases h with ⟨rfl, ha⟩ | ⟨rfl, ha⟩
  · have : (1 : ℝ) ≤ a := by exact_mod_cast ha
    push_cast; nlinarith
  · have : (3 : ℝ) ≤ a := by exact_mod_cast ha
    push_cast; nlinarith

theorem discr_cast (a : ℕ) (E : ℤ) : ((discr a E : ℤ) : ℝ) = (a : ℝ) ^ 2 + 4 * E := by
  unfold discr; push_cast; ring

theorem sqrtD_sq (h : Adm a E) : Real.sqrt ((a : ℝ) ^ 2 + 4 * E) ^ 2 = (a : ℝ) ^ 2 + 4 * E :=
  Real.sq_sqrt (by linarith [discr_ge h])

theorem sqrtD_gt_two (h : Adm a E) : 2 < Real.sqrt ((a : ℝ) ^ 2 + 4 * E) := by
  rw [show (2 : ℝ) = Real.sqrt 4 by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_lt_sqrt (by norm_num) (by linarith [discr_ge h])

theorem eps_add (a : ℕ) (E : ℤ) : epsU a E + epsBar a E = a := by
  unfold epsU epsBar; ring

theorem eps_sub (a : ℕ) (E : ℤ) : epsU a E - epsBar a E = Real.sqrt ((a : ℝ) ^ 2 + 4 * E) := by
  unfold epsU epsBar; ring

theorem eps_mul (h : Adm a E) : epsU a E * epsBar a E = -E := by
  unfold epsU epsBar
  have := sqrtD_sq h
  linear_combination (-1 / 4 : ℝ) * this

theorem eps_gt_one (h : Adm a E) : 1 < epsU a E := by
  have h2 := sqrtD_gt_two h
  have : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  unfold epsU; linarith

theorem eps_quad (h : Adm a E) : epsU a E ^ 2 = a * epsU a E + E := by
  have h1 := eps_add a E
  have h2 := eps_mul h
  have : epsBar a E = a - epsU a E := by linarith
  rw [this] at h2; linear_combination -h2

theorem epsBar_quad (h : Adm a E) : epsBar a E ^ 2 = a * epsBar a E + E := by
  have h1 := eps_add a E
  have h2 := eps_mul h
  have : epsU a E = a - epsBar a E := by linarith
  rw [this] at h2; linear_combination -h2

theorem epsBar_ne_zero (h : Adm a E) : epsBar a E ≠ 0 := by
  intro h0
  have := eps_mul h
  rw [h0, mul_zero] at this
  rcases h with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> norm_num at this

theorem abs_epsBar_lt_one (h : Adm a E) : |epsBar a E| < 1 := by
  have he := eps_gt_one h
  have hm := eps_mul h
  have habs : epsU a E * |epsBar a E| = 1 := by
    have : |epsU a E * epsBar a E| = 1 := by
      rw [hm, abs_neg]; rcases h with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> norm_num
    rw [abs_mul, abs_of_pos (by linarith)] at this; exact this
  nlinarith [abs_nonneg (epsBar a E)]

/-- Binet: `√Δ U_m = ε^m − ε̄^m`. -/
theorem binet (h : Adm a E) (m : ℕ) :
    (lucasU a E m : ℝ) * Real.sqrt ((a : ℝ) ^ 2 + 4 * E) = epsU a E ^ m - epsBar a E ^ m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    match m, ih with
    | 0, _ => simp [lucasU]
    | 1, _ => simp [lucasU, eps_sub]
    | (m + 2), ih =>
      have h1 := ih (m + 1) (by omega)
      have h0 := ih m (by omega)
      simp only [lucasU]
      push_cast
      have q1 := eps_quad h
      have q2 := epsBar_quad h
      calc ((a : ℝ) * (lucasU a E (m + 1) : ℝ) + (E : ℝ) * (lucasU a E m : ℝ)) *
            Real.sqrt ((a : ℝ) ^ 2 + 4 * E)
          = a * ((lucasU a E (m + 1) : ℝ) * Real.sqrt ((a : ℝ) ^ 2 + 4 * E)) +
            E * ((lucasU a E m : ℝ) * Real.sqrt ((a : ℝ) ^ 2 + 4 * E)) := by ring
        _ = epsU a E ^ (m + 2) - epsBar a E ^ (m + 2) := by
          rw [h1, h0]
          linear_combination (-(epsU a E ^ m)) * q1 + epsBar a E ^ m * q2

theorem lucasU_ne_zero (h : Adm a E) {m : ℕ} (hm : 1 ≤ m) : (lucasU a E m : ℝ) ≠ 0 := by
  intro h0
  have hb := binet h m
  rw [h0, zero_mul] at hb
  have h1 : 1 < epsU a E ^ m := one_lt_pow₀ (eps_gt_one h) (by omega)
  have h2 : |epsBar a E ^ m| < 1 := by
    rw [abs_pow]; exact pow_lt_one₀ (abs_nonneg _) (abs_epsBar_lt_one h) (by omega)
  have : epsU a E ^ m = epsBar a E ^ m := by linarith
  rw [← this, abs_of_pos (by linarith)] at h2
  linarith

theorem qU_ne_zero (h : Adm a E) : qU a E ≠ 0 :=
  div_ne_zero (epsBar_ne_zero h) (by linarith [eps_gt_one h])

theorem abs_qU_lt_one (h : Adm a E) : |qU a E| < 1 := by
  unfold qU
  have he := eps_gt_one h
  rw [abs_div, abs_of_pos (show 0 < epsU a E by linarith),
    div_lt_one (show 0 < epsU a E by linarith)]
  linarith [abs_epsBar_lt_one h]

/-- The trace `s = q + q⁻¹ = −E a² − 2`. -/
def sU (a : ℕ) (E : ℤ) : ℤ := -E * (a : ℤ) ^ 2 - 2

theorem qU_add_inv (h : Adm a E) : qU a E + (qU a E)⁻¹ = sU a E := by
  have he : epsU a E ≠ 0 := by linarith [eps_gt_one h]
  have hb := epsBar_ne_zero h
  have hm := eps_mul h
  have hs := eps_add a E
  have hE' : (E : ℝ) ^ 2 = 1 := by exact_mod_cast E_sq h
  have hEne : (E : ℝ) ≠ 0 := by intro h0; rw [h0] at hE'; norm_num at hE'
  have hsq : epsBar a E ^ 2 + epsU a E ^ 2 = (a : ℝ) ^ 2 + 2 * E := by
    have : epsBar a E ^ 2 + epsU a E ^ 2 =
        (epsU a E + epsBar a E) ^ 2 - 2 * (epsU a E * epsBar a E) := by ring
    rw [this, hs, hm]; ring
  have key : qU a E + (qU a E)⁻¹ = (epsBar a E ^ 2 + epsU a E ^ 2) / (epsU a E * epsBar a E) := by
    unfold qU; rw [inv_div]; field_simp
  rw [key, hsq, hm, div_eq_iff (neg_ne_zero.mpr hEne)]
  unfold sU; push_cast
  linear_combination (-(a : ℝ) ^ 2) * hE'

theorem discr_mul_sq (h : Adm a E) : IsSquare (discr a E * (sU a E ^ 2 - 4)) := by
  refine ⟨(a : ℤ) * discr a E, ?_⟩
  have hE := E_sq h
  unfold discr sU
  linear_combination (((a : ℤ) ^ 2 + 4 * E) * (a : ℤ) ^ 4) * hE
theorem discr_pos (h : Adm a E) : 0 < discr a E := by
  have := discr_ge h
  have : (0 : ℝ) < ((discr a E : ℤ) : ℝ) := by rw [discr_cast]; linarith
  exact_mod_cast this

/-- Termwise: `m² (U_{m+1}/U_m − ε) = √Δ · m² q^m/(1 − q^m)`. -/
theorem term_eq (h : Adm a E) (m : ℕ) :
    (m : ℝ) ^ 2 * ((lucasU a E (m + 1) : ℝ) / lucasU a E m - epsU a E) =
      Real.sqrt ((a : ℝ) ^ 2 + 4 * E) * ((m : ℝ) ^ 2 * qU a E ^ m / (1 - qU a E ^ m)) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  have hU := lucasU_ne_zero h hm
  have hS : Real.sqrt ((a : ℝ) ^ 2 + 4 * E) ≠ 0 := by linarith [sqrtD_gt_two h]
  have he : epsU a E ≠ 0 := by linarith [eps_gt_one h]
  have hb0 := binet h m
  have hb1 := binet h (m + 1)
  have hεm : epsU a E ^ m ≠ 0 := pow_ne_zero _ he
  have hden : epsU a E ^ m - epsBar a E ^ m ≠ 0 := by
    rw [← hb0]; exact mul_ne_zero hU hS
  have hq : qU a E ^ m = epsBar a E ^ m / epsU a E ^ m := by unfold qU; rw [div_pow]
  have h1q : 1 - qU a E ^ m = (epsU a E ^ m - epsBar a E ^ m) / epsU a E ^ m := by
    rw [hq]; field_simp
  rw [h1q, hq]
  -- U_{m+1}/U_m − ε = ε̄^m / U_m = √Δ ε̄^m/(ε^m − ε̄^m)
  have hU' : (lucasU a E m : ℝ) = (epsU a E ^ m - epsBar a E ^ m) / Real.sqrt ((a : ℝ) ^ 2 + 4 * E) := by
    field_simp; linarith
  have hU1 : (lucasU a E (m + 1) : ℝ) =
      (epsU a E ^ (m + 1) - epsBar a E ^ (m + 1)) / Real.sqrt ((a : ℝ) ^ 2 + 4 * E) := by
    field_simp; linarith
  rw [hU', hU1]
  have hsub := eps_sub a E
  field_simp
  rw [← hsub]
  ring

end QZeta3
