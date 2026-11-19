import Mathlib

/-!
# Definitions (frozen)

Source proof: `handoff/fibzeta/many/PROOF_T1.md` (case A = 4, r = 1, so e = k = n).

## Objects in the final statements
* `zetaq3 q = Σ_{m ≥ 1} m² q^m / (1 − q^m)` (the `m = 0` term is `0` in Lean).
* `lucasU a E`: `U₀ = 0`, `U₁ = 1`, `U_{m+2} = a U_{m+1} + E U_m`; `epsU a E = (a + √(a² + 4E))/2`.

## The construction (internal; generic over a field `𝕜`)
* `qPoch x q m = (x; q)_m = ∏_{i<m} (1 − x qⁱ)`.
* `Rfun n q T = R_n(T; q) = (q;q)_n² (q^{−n}T;q)_n (q^{n+1}T;q)_n Tⁿ / (T;q)_{n+1}⁴` (PROOF_T1 §1).
* `Npoly n q ∈ 𝕜[T]`: the numerator of `R_n`, as a polynomial in `T`.
* `Gser n q j ∈ 𝕜⟦u⟧`: the expansion of `u⁴ R_n(T)` at the pole `T = q^{−j}`, in `u = 1 − q^j T`,
  i.e. `N(q^{−j}(1−u)) · (∏_{j' ≠ j} (1 − q^{j'} q^{−j}(1−u))⁴)⁻¹`.
* `cc n q s j = c_{s,j} = [u^{4−s}] Gser n q j`: the partial-fraction coefficients (2.1).
* `P3 = Σ_j (c_{3,j} + 2 c_{4,j})` and `P0 = −Σ_{s,j} c_{s,j} W_{s,j}` (Lemma 4).
* `dn n x = d_n(x) = ∏_{ℓ=1}^{n} Φ_ℓ(x)`; `Sn n q = Σ_{k≥1} R(q^k) − Σ_{k≥1} R(q^{−n−k})` (§3).
* `LaurentInt f`: `f` agrees, at every real `x ≠ 0` with `|x| ≠ 1`, with one fixed integer
  Laurent polynomial.
-/

open Polynomial Finset

namespace QZeta3

/-! ### Objects in the final statements -/

/-- `ζ_q(3) = Σ_{m ≥ 1} m² q^m / (1 − q^m)`. -/
noncomputable def zetaq3 (q : ℝ) : ℝ := ∑' m : ℕ, (m : ℝ) ^ 2 * q ^ m / (1 - q ^ m)

/-- The Lucas sequence `U₀ = 0`, `U₁ = 1`, `U_{m+2} = a U_{m+1} + E U_m`. -/
def lucasU (a : ℕ) (E : ℤ) : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | (m + 2) => a * lucasU a E (m + 1) + E * lucasU a E m

/-- The dominant root `ε = (a + √(a² + 4E))/2` of `X² − aX − E`. -/
noncomputable def epsU (a : ℕ) (E : ℤ) : ℝ := (a + Real.sqrt ((a : ℝ) ^ 2 + 4 * E)) / 2

/-! ### The construction -/

noncomputable section Generic

variable {𝕜 : Type*} [Field 𝕜]

/-- `(x; q)_m = ∏_{i<m} (1 − x qⁱ)`. -/
def qPoch (x q : 𝕜) (m : ℕ) : 𝕜 := ∏ i ∈ range m, (1 - x * q ^ i)

/-- `R_n(T; q)` for `A = 4`, `r = 1` (PROOF_T1 §1). -/
def Rfun (n : ℕ) (q T : 𝕜) : 𝕜 :=
  qPoch q q n ^ 2 * qPoch ((q ^ n)⁻¹ * T) q n * qPoch (q ^ (n + 1) * T) q n * T ^ n /
    qPoch T q (n + 1) ^ 4

/-- `(x; q)_m` with `x = y·T`, as a polynomial in `T`: `∏_{i<m} (1 − y qⁱ T)`. -/
def qPochPoly (y q : 𝕜) (m : ℕ) : 𝕜[X] := ∏ i ∈ range m, (1 - C (y * q ^ i) * X)

/-- The numerator of `R_n` as a polynomial in `T`. -/
def Npoly (n : ℕ) (q : 𝕜) : 𝕜[X] :=
  C (qPoch q q n ^ 2) * qPochPoly (q ^ n)⁻¹ q n * qPochPoly (q ^ (n + 1)) q n * X ^ n

/-- `T = q^{−j}(1 − u)`, as a polynomial in `u`. -/
def Tsub (q : 𝕜) (j : ℕ) : 𝕜[X] := C (q ^ j)⁻¹ * (1 - X)

/-- `∏_{j' ≠ j, j' ≤ n} (1 − q^{j'} T)⁴` at `T = q^{−j}(1 − u)`, as a polynomial in `u`. -/
def Dother (n : ℕ) (q : 𝕜) (j : ℕ) : 𝕜[X] :=
  ∏ j' ∈ (range (n + 1)).erase j, (1 - C (q ^ j') * Tsub q j) ^ 4

/-- The expansion of `u⁴ R_n(T)` at the pole `T = q^{−j}`, in the variable `u = 1 − q^j T`. -/
noncomputable def Gser (n : ℕ) (q : 𝕜) (j : ℕ) : PowerSeries 𝕜 :=
  ((Npoly n q).comp (Tsub q j) : PowerSeries 𝕜) * (Dother n q j : PowerSeries 𝕜)⁻¹

/-- The partial-fraction coefficient `c_{s,j}` of `(1 − q^j T)^{−s}` in `R_n` (1 ≤ s ≤ 4). -/
noncomputable def cc (n : ℕ) (q : 𝕜) (s j : ℕ) : 𝕜 := PowerSeries.coeff (4 - s) (Gser n q j)

/-- `P₃ = 2 Q₂ = Σ_j (c_{3,j} + 2 c_{4,j})`. -/
noncomputable def P3 (n : ℕ) (q : 𝕜) : 𝕜 := ∑ j ∈ range (n + 1), (cc n q 3 j + 2 * cc n q 4 j)

/-- `W_{s,j} = Σ_{m=1}^{j} ((1 − q^m)^{−s} − 1) − Σ_{m=1}^{n−j} (1 − q^{−m})^{−s}`. -/
def Wf (n : ℕ) (q : 𝕜) (s j : ℕ) : 𝕜 :=
  ∑ m ∈ Icc 1 j, (((1 - q ^ m) ^ s)⁻¹ - 1) - ∑ m ∈ Icc 1 (n - j), ((1 - (q ^ m)⁻¹) ^ s)⁻¹

/-- `P₀ = −Σ_{s,j} c_{s,j} W_{s,j}`. -/
noncomputable def P0 (n : ℕ) (q : 𝕜) : 𝕜 :=
  -∑ j ∈ range (n + 1), ∑ s ∈ Icc 1 4, cc n q s j * Wf n q s j

end Generic

/-- `d_n(x) = ∏_{ℓ=1}^{n} Φ_ℓ(x)`. -/
noncomputable def dn (n : ℕ) (x : ℝ) : ℝ := ∏ ℓ ∈ Icc 1 n, aeval x (cyclotomic ℓ ℤ)

/-- The linear form `S_n(q) = Σ_{k≥1} R_n(q^k) − Σ_{k≥1} R_n(q^{−n−k})`. -/
noncomputable def Sn (n : ℕ) (q : ℝ) : ℝ :=
  ∑' k : ℕ, Rfun n q (q ^ (k + 1)) - ∑' k : ℕ, Rfun n q (q ^ (n + k + 1))⁻¹

/-- `f` is, uniformly in every real `x ≠ 0` with `|x| ≠ 1`, the value of one integer Laurent
polynomial `x^{−c} p(x)`. -/
def LaurentInt (f : ℝ → ℝ) : Prop :=
  ∃ (p : ℤ[X]) (c : ℕ), ∀ x : ℝ, x ≠ 0 → |x| ≠ 1 → x ^ c * f x = aeval x p

end QZeta3
