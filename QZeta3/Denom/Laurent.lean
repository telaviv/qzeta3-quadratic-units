import QZeta3.Statements

/-!
# Closure properties of `LaurentInt`

`LaurentInt f` says that `f` agrees, at every real `x ≠ 0` with `|x| ≠ 1`, with one fixed integer
Laurent polynomial. It is closed under constants, `x`, `x⁻¹`, `+`, `−`, `×`, powers and finite
sums and products. We also record the two facts about admissible points that are used throughout:
`x^m ≠ 1` for `m ≥ 1`, and `m ↦ x^m` is injective.
-/

open Polynomial Finset

namespace QZeta3.LaurentInt

theorem congr {f g : ℝ → ℝ} (hf : LaurentInt f)
    (h : ∀ x : ℝ, x ≠ 0 → |x| ≠ 1 → f x = g x) : LaurentInt g := by
  obtain ⟨p, c, hp⟩ := hf
  exact ⟨p, c, fun x hx hx1 => by rw [← h x hx hx1]; exact hp x hx hx1⟩

theorem aeval (p : ℤ[X]) : LaurentInt (fun x => Polynomial.aeval x p) :=
  ⟨p, 0, fun x _ _ => by simp⟩

theorem intCast (z : ℤ) : LaurentInt (fun _ => (z : ℝ)) :=
  ⟨C z, 0, fun x _ _ => by simp⟩

theorem zero : LaurentInt (fun _ => 0) := by
  simpa using LaurentInt.intCast 0

theorem one : LaurentInt (fun _ => 1) := by
  simpa using LaurentInt.intCast 1

theorem id : LaurentInt (fun x => x) :=
  ⟨X, 0, fun x _ _ => by simp⟩

theorem inv_id : LaurentInt (fun x => x⁻¹) :=
  ⟨1, 1, fun x hx _ => by simp [hx]⟩

theorem add {f g : ℝ → ℝ} (hf : LaurentInt f) (hg : LaurentInt g) :
    LaurentInt (fun x => f x + g x) := by
  obtain ⟨p, c, hp⟩ := hf
  obtain ⟨p', c', hp'⟩ := hg
  refine ⟨X ^ c' * p + X ^ c * p', c + c', fun x hx hx1 => ?_⟩
  simp only [map_add, map_mul, map_pow, aeval_X]
  rw [← hp x hx hx1, ← hp' x hx hx1]
  ring

theorem mul {f g : ℝ → ℝ} (hf : LaurentInt f) (hg : LaurentInt g) :
    LaurentInt (fun x => f x * g x) := by
  obtain ⟨p, c, hp⟩ := hf
  obtain ⟨p', c', hp'⟩ := hg
  refine ⟨p * p', c + c', fun x hx hx1 => ?_⟩
  rw [map_mul, ← hp x hx hx1, ← hp' x hx hx1]
  ring

theorem neg {f : ℝ → ℝ} (hf : LaurentInt f) : LaurentInt (fun x => -f x) := by
  obtain ⟨p, c, hp⟩ := hf
  refine ⟨-p, c, fun x hx hx1 => ?_⟩
  rw [map_neg, ← hp x hx hx1]
  ring

theorem sub {f g : ℝ → ℝ} (hf : LaurentInt f) (hg : LaurentInt g) :
    LaurentInt (fun x => f x - g x) :=
  (hf.add hg.neg).congr fun x _ _ => by ring

theorem pow {f : ℝ → ℝ} (hf : LaurentInt f) (k : ℕ) :
    LaurentInt (fun x => f x ^ k) := by
  induction k with
  | zero => simpa using LaurentInt.one
  | succ k ih => exact (ih.mul hf).congr fun x _ _ => by ring

theorem sum {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℝ}
    (h : ∀ i ∈ s, LaurentInt (f i)) : LaurentInt (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using LaurentInt.zero
  | insert a s ha ih =>
    have := (h a (mem_insert_self a s)).add (ih fun i hi => h i (mem_insert_of_mem hi))
    simpa [sum_insert ha] using this

theorem prod {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℝ}
    (h : ∀ i ∈ s, LaurentInt (f i)) : LaurentInt (fun x => ∏ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using LaurentInt.one
  | insert a s ha ih =>
    have := (h a (mem_insert_self a s)).mul (ih fun i hi => h i (mem_insert_of_mem hi))
    simpa [prod_insert ha] using this

theorem pow_id (k : ℕ) : LaurentInt (fun x => x ^ k) := LaurentInt.id.pow k

theorem inv_pow_id (k : ℕ) : LaurentInt (fun x => (x ^ k)⁻¹) :=
  (LaurentInt.inv_id.pow k).congr fun x _ _ => by rw [inv_pow]

end QZeta3.LaurentInt

namespace QZeta3.Denom

/-! ### Admissible points -/

theorem pow_ne_one_of_adm {x : ℝ} (_hx : x ≠ 0) (hx1 : |x| ≠ 1) {m : ℕ} (hm : m ≠ 0) :
    x ^ m ≠ 1 := by
  intro h
  have : |x| ^ m = 1 := by rw [← abs_pow, h, abs_one]
  exact hx1 ((pow_eq_one_iff_of_nonneg (abs_nonneg x) hm).1 this)

theorem pow_inj_of_adm {x : ℝ} (hx : x ≠ 0) (hx1 : |x| ≠ 1) {a b : ℕ} (h : x ^ a = x ^ b) :
    a = b := by
  have : |x| ^ a = |x| ^ b := by rw [← abs_pow, ← abs_pow, h]
  exact pow_right_injective₀ (abs_pos.2 hx) hx1 this

theorem one_sub_pow_ne_zero {x : ℝ} (hx : x ≠ 0) (hx1 : |x| ≠ 1) {m : ℕ} (hm : m ≠ 0) :
    1 - x ^ m ≠ 0 :=
  sub_ne_zero.2 (Ne.symm (pow_ne_one_of_adm hx hx1 hm))

/-- `1 − x^a x^{−b} ≠ 0` for `a ≠ b`. -/
theorem one_sub_pow_mul_inv_ne_zero {x : ℝ} (hx : x ≠ 0) (hx1 : |x| ≠ 1) {a b : ℕ}
    (hab : a ≠ b) : 1 - x ^ a * (x ^ b)⁻¹ ≠ 0 := by
  intro h
  have h' : x ^ a * (x ^ b)⁻¹ = 1 := by linarith
  rw [mul_inv_eq_one₀ (pow_ne_zero _ hx)] at h'
  exact hab (pow_inj_of_adm hx hx1 h')

end QZeta3.Denom
