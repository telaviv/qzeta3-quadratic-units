import QZeta3.Denom.Cyclo

/-!
# Power series with `d_n`-integral coefficients

`SerInt n F` (for a family `F x` of power series in `u`, indexed by the real point `x`) says that for
every `K`, `x ↦ d_n(x)^K · [u^K] F x` is `LaurentInt`. This is closed under constants, `u`, `+`, `−`,
`×`, finite sums and products, and powers (the product rule is the Cauchy product with
`d_n^K = d_n^a · d_n^b` for `a + b = K`). The geometric series
`u/(α + βu) = Σ_{K≥1} (−β)^{K−1} α^{−K} u^K` is `SerInt` when `β` and `d_n/α` are `LaurentInt`
(PROOF_T1 Lemma 3, "the coefficient of u^M").
-/

open Finset

namespace QZeta3.Denom

/-- `[u^K] F x` has denominator dividing `d_n(x)^K`, uniformly in `x`. -/
def SerInt (n : ℕ) (F : ℝ → PowerSeries ℝ) : Prop :=
  ∀ K : ℕ, LaurentInt (fun x => dn n x ^ K * PowerSeries.coeff K (F x))

variable {n : ℕ}

theorem SerInt.congr {F G : ℝ → PowerSeries ℝ} (hF : SerInt n F)
    (h : ∀ x : ℝ, x ≠ 0 → |x| ≠ 1 → F x = G x) : SerInt n G :=
  fun K => (hF K).congr fun x hx hx1 => by rw [h x hx hx1]

theorem SerInt.C {f : ℝ → ℝ} (hf : LaurentInt f) : SerInt n (fun x => PowerSeries.C (f x)) := by
  intro K
  rcases K with _ | K
  · simpa using hf
  · simpa [PowerSeries.coeff_C] using LaurentInt.zero

theorem SerInt.one : SerInt n (fun _ => 1) :=
  (SerInt.C LaurentInt.one).congr fun _ _ _ => map_one _

theorem SerInt.X : SerInt n (fun _ => PowerSeries.X) := by
  intro K
  rcases K with _ | _ | K
  · simpa [PowerSeries.coeff_X] using LaurentInt.zero
  · simpa [PowerSeries.coeff_X] using dn_laurent n
  · simpa [PowerSeries.coeff_X] using LaurentInt.zero

theorem SerInt.add {F G : ℝ → PowerSeries ℝ} (hF : SerInt n F) (hG : SerInt n G) :
    SerInt n (fun x => F x + G x) :=
  fun K => ((hF K).add (hG K)).congr fun x _ _ => by rw [map_add]; ring

theorem SerInt.neg {F : ℝ → PowerSeries ℝ} (hF : SerInt n F) : SerInt n (fun x => -F x) :=
  fun K => (hF K).neg.congr fun x _ _ => by rw [map_neg]; ring

theorem SerInt.sub {F G : ℝ → PowerSeries ℝ} (hF : SerInt n F) (hG : SerInt n G) :
    SerInt n (fun x => F x - G x) :=
  (hF.add hG.neg).congr fun x _ _ => by ring

theorem SerInt.mul {F G : ℝ → PowerSeries ℝ} (hF : SerInt n F) (hG : SerInt n G) :
    SerInt n (fun x => F x * G x) := by
  intro K
  refine (LaurentInt.sum (antidiagonal K)
    (f := fun p x => dn n x ^ p.1 * PowerSeries.coeff p.1 (F x) *
      (dn n x ^ p.2 * PowerSeries.coeff p.2 (G x)))
    fun p _ => (hF p.1).mul (hG p.2)).congr fun x _ _ => ?_
  rw [PowerSeries.coeff_mul, mul_sum]
  refine sum_congr rfl fun p hp => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  rw [← hp, pow_add]
  ring

theorem SerInt.pow {F : ℝ → PowerSeries ℝ} (hF : SerInt n F) (k : ℕ) :
    SerInt n (fun x => F x ^ k) := by
  induction k with
  | zero => exact SerInt.one.congr fun x _ _ => (pow_zero _).symm
  | succ k ih => exact (ih.mul hF).congr fun x _ _ => (pow_succ _ _).symm

theorem SerInt.sum {ι : Type*} (s : Finset ι) {F : ι → ℝ → PowerSeries ℝ}
    (h : ∀ i ∈ s, SerInt n (F i)) : SerInt n (fun x => ∑ i ∈ s, F i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact (SerInt.C LaurentInt.zero).congr fun x _ _ => by simp
  | insert a s ha ih =>
    exact ((h a (mem_insert_self a s)).add (ih fun i hi => h i (mem_insert_of_mem hi))).congr
      fun x _ _ => by rw [sum_insert ha]

/-- `u/(α + βu) = Σ_{K ≥ 1} (−β)^{K−1} α^{−K} u^K`. -/
noncomputable def geom (α β : ℝ) : PowerSeries ℝ :=
  PowerSeries.mk fun k => if k = 0 then 0 else (-β) ^ (k - 1) * α⁻¹ ^ k

theorem SerInt.geom {α β : ℝ → ℝ} (hβ : LaurentInt β)
    (hα : LaurentInt (fun x => dn n x * (α x)⁻¹)) :
    SerInt n (fun x => geom (α x) (β x)) := by
  intro K
  rcases K with _ | K
  · simpa [Denom.geom] using LaurentInt.zero
  · refine ((hβ.neg.pow K).mul (hα.pow (K + 1))).congr fun x _ _ => ?_
    simp only [Denom.geom, PowerSeries.coeff_mk, ite_eq_right (show K + 1 ≠ 0 by omega),
      Nat.add_sub_cancel]
    ring

theorem geom_mul {α β : ℝ} (hα : α ≠ 0) :
    geom α β * (PowerSeries.C α + PowerSeries.C β * PowerSeries.X) = PowerSeries.X := by
  ext k
  rw [mul_add, map_add, PowerSeries.coeff_mul_C, ← mul_assoc]
  rcases k with _ | _ | k
  · simp [geom]
  · rw [PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_mul_C]
    simp [geom, hα]
  · rw [PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_mul_C]
    simp only [geom, PowerSeries.coeff_mk, PowerSeries.coeff_X,
      ite_eq_right (show k + 1 + 1 ≠ 0 by omega), ite_eq_right (show k + 1 ≠ 0 by omega),
      ite_eq_right (show k + 1 + 1 ≠ 1 by omega), Nat.add_sub_cancel]
    have h1 : α⁻¹ * α = 1 := inv_mul_cancel₀ hα
    linear_combination ((-β) ^ k * α⁻¹ ^ (k + 1) * (-β)) * h1

theorem X_mul_inv_eq_geom {α β : ℝ} (hα : α ≠ 0) :
    PowerSeries.X * (PowerSeries.C α + PowerSeries.C β * PowerSeries.X)⁻¹ = geom α β := by
  have hc : PowerSeries.constantCoeff (PowerSeries.C α + PowerSeries.C β * PowerSeries.X) ≠ 0 := by
    simp [hα]
  calc PowerSeries.X * (PowerSeries.C α + PowerSeries.C β * PowerSeries.X)⁻¹
      = geom α β * (PowerSeries.C α + PowerSeries.C β * PowerSeries.X) *
        (PowerSeries.C α + PowerSeries.C β * PowerSeries.X)⁻¹ := by rw [geom_mul hα]
    _ = geom α β := by rw [mul_assoc, PowerSeries.mul_inv_cancel _ hc, mul_one]

end QZeta3.Denom
