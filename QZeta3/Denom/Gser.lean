import QZeta3.Denom.Weights
import QZeta3.Denom.SerInt

/-!
# The factorisation of `Gser` and its `d_n`-integrality

Fix an admissible `x` and a pole index `j ≤ n`. With `u = 1 − x^j T`, each linear factor
`1 − x^{j''} T` becomes `α_{j''} + β_{j''} u` (`α = 1 − x^{j''−j}`, `β = x^{j''−j}`); for `j'' = j`
it is `u`. Put `L = ∏_{j'' ≠ j} (α_{j''} + β_{j''} u)`, so `Dother = L⁴`.

For a numerator `N` of degree `≤ n`, the simple partial fractions give, in `ℝ⟦u⟧`,
  `N(T(u)) = E(N) · L`,  `E(N) = wt_j + Σ_{j' ≠ j} wt_{j'} · u/(α_{j'} + β_{j'} u)`.
Hence (PROOF_T1 Lemma 3) `Gser = T(u)ⁿ · E(N1)² · E(N3) · E(N4)`, and every factor is `SerInt`.
-/

open Polynomial Finset

namespace QZeta3.Denom

/-- `α_{j'} = 1 − x^{j'} x^{−j}`. -/
noncomputable def αf (x : ℝ) (j j' : ℕ) : ℝ := 1 - x ^ j' * (x ^ j)⁻¹

/-- `β_{j'} = x^{j'} x^{−j}`. -/
noncomputable def βf (x : ℝ) (j j' : ℕ) : ℝ := x ^ j' * (x ^ j)⁻¹

/-- `1 − x^{j''} T` at `T = x^{−j}(1 − u)`, as a power series in `u`. -/
noncomputable def linS (x : ℝ) (j j'' : ℕ) : PowerSeries ℝ :=
  PowerSeries.C (αf x j j'') + PowerSeries.C (βf x j j'') * PowerSeries.X

/-- `L = ∏_{j'' ≠ j} (1 − x^{j''} T(u))`. -/
noncomputable def Lps (x : ℝ) (n j : ℕ) : PowerSeries ℝ :=
  ∏ j'' ∈ (range (n + 1)).erase j, linS x j j''

/-- `E(w) = w_j + Σ_{j' ≠ j} w_{j'} · u/(α_{j'} + β_{j'} u)`. -/
noncomputable def Ef (n : ℕ) (x : ℝ) (j : ℕ) (w : ℕ → ℝ) : PowerSeries ℝ :=
  PowerSeries.C (w j) +
    ∑ j' ∈ (range (n + 1)).erase j, PowerSeries.C (w j') * geom (αf x j j') (βf x j j')

theorem coe_lin (x : ℝ) (j j'' : ℕ) :
    ((1 - C (x ^ j'') * Tsub x j : ℝ[X]) : PowerSeries ℝ) = linS x j j'' := by
  have h : (1 - C (x ^ j'') * Tsub x j : ℝ[X]) = C (αf x j j'') + C (βf x j j'') * X := by
    simp only [Tsub, αf, βf, map_sub, map_one, map_mul]
    ring
  rw [h, linS]
  simp

theorem linS_self {x : ℝ} (hx : x ≠ 0) (j : ℕ) : linS x j j = PowerSeries.X := by
  simp [linS, αf, βf, mul_inv_cancel₀ (pow_ne_zero j hx)]

theorem αf_ne_zero {x : ℝ} (hx : x ≠ 0) (hx1 : |x| ≠ 1) {j j' : ℕ} (h : j' ≠ j) :
    αf x j j' ≠ 0 :=
  one_sub_pow_mul_inv_ne_zero hx hx1 h

theorem constantCoeff_linS (x : ℝ) (j j' : ℕ) :
    PowerSeries.constantCoeff (linS x j j') = αf x j j' := by
  simp [linS]

/-- Regrouping `Σ_{j'} a_{j'} ∏_{j'' ≠ j'} ℓ_{j''}` around the factor `ℓ_j = u`. -/
theorem sum_prod_erase_eq {S : Finset ℕ} {j : ℕ} (hj : j ∈ S) (ℓ : ℕ → PowerSeries ℝ)
    (a : ℕ → ℝ) (hℓj : ℓ j = PowerSeries.X)
    (hℓ : ∀ j' ∈ S, j' ≠ j → PowerSeries.constantCoeff (ℓ j') ≠ 0) :
    ∑ j' ∈ S, PowerSeries.C (a j') * ∏ j'' ∈ S.erase j', ℓ j'' =
      (PowerSeries.C (a j) + ∑ j' ∈ S.erase j, PowerSeries.C (a j') * (PowerSeries.X * (ℓ j')⁻¹)) *
        ∏ j'' ∈ S.erase j, ℓ j'' := by
  rw [← add_sum_erase S _ hj, add_mul, sum_mul]
  congr 1
  refine sum_congr rfl fun j' hj' => ?_
  obtain ⟨hne, hj'S⟩ := mem_erase.1 hj'
  rw [← mul_prod_erase (S.erase j) ℓ (mem_erase.2 ⟨hne, hj'S⟩),
    ← mul_prod_erase (S.erase j') ℓ (mem_erase.2 ⟨Ne.symm hne, hj⟩),
    erase_right_comm (s := S) (a := j') (b := j), hℓj]
  have h1 := PowerSeries.inv_mul_cancel (ℓ j') (hℓ j' hj'S hne)
  linear_combination (-(PowerSeries.C (a j') * PowerSeries.X *
    ∏ j'' ∈ (S.erase j).erase j', ℓ j'')) * h1

theorem comp_eq {x : ℝ} (hx : x ≠ 0) (hx1 : |x| ≠ 1) {n j : ℕ} (hj : j ∈ range (n + 1))
    (N : ℝ[X]) (hN : N.natDegree ≤ n) :
    ((N.comp (Tsub x j) : ℝ[X]) : PowerSeries ℝ) = Ef n x j (wt n x N) * Lps x n j := by
  have hL : ((N.comp (Tsub x j) : ℝ[X]) : PowerSeries ℝ) =
      ∑ j' ∈ range (n + 1), PowerSeries.C (wt n x N j') *
        ∏ j'' ∈ (range (n + 1)).erase j', linS x j j'' := by
    conv_lhs => rw [lagrange hx hx1 n N hN]
    simp only [Polynomial.sum_comp, mul_comp, C_comp, lagPoly, Polynomial.prod_comp, sub_comp,
      one_comp, X_comp]
    rw [← coeToPowerSeries.ringHom_apply, map_sum]
    refine sum_congr rfl fun j' _ => ?_
    rw [map_mul, map_prod, coeToPowerSeries.ringHom_apply, Polynomial.coe_C]
    congr 1
    exact prod_congr rfl fun j'' _ => by rw [coeToPowerSeries.ringHom_apply, coe_lin]
  rw [hL, Ef, Lps, sum_prod_erase_eq hj (linS x j) (wt n x N) (linS_self hx j)
    (fun j' _ hne => by rw [constantCoeff_linS]; exact αf_ne_zero hx hx1 hne)]
  congr 1
  congr 1
  refine sum_congr rfl fun j' hj' => ?_
  rw [linS, X_mul_inv_eq_geom (αf_ne_zero hx hx1 (mem_erase.1 hj').1)]

theorem Gser_eq {x : ℝ} (hx : x ≠ 0) (hx1 : |x| ≠ 1) {n j : ℕ} (hj : j ∈ range (n + 1)) :
    Gser n x j = ((Tsub x j : ℝ[X]) : PowerSeries ℝ) ^ n *
      (Ef n x j (wt n x (N1 n x)) * Ef n x j (wt n x (N1 n x)) * Ef n x j (wt n x (N3 n x)) *
        Ef n x j (wt n x (N4 n x))) := by
  have hN : Npoly n x = N1 n x * N1 n x * N3 n x * N4 n x * X ^ n := by
    simp only [Npoly, N1, N3, N4, map_pow]
    ring
  have hD : ((Dother n x j : ℝ[X]) : PowerSeries ℝ) = Lps x n j ^ 4 := by
    rw [Dother, prod_pow, Polynomial.coe_pow, Lps, ← coeToPowerSeries.ringHom_apply, map_prod]
    congr 1
    exact prod_congr rfl fun j'' _ => by rw [coeToPowerSeries.ringHom_apply, coe_lin]
  have hc : PowerSeries.constantCoeff (Lps x n j ^ 4) ≠ 0 := by
    rw [map_pow, Lps, map_prod]
    exact pow_ne_zero _ (prod_ne_zero_iff.2 fun j' hj' => by
      rw [constantCoeff_linS]; exact αf_ne_zero hx hx1 (mem_erase.1 hj').1)
  rw [Gser, hD, hN]
  simp only [mul_comp, X_pow_comp, Polynomial.coe_mul, Polynomial.coe_pow]
  rw [comp_eq hx hx1 hj _ (natDegree_N1 n x), comp_eq hx hx1 hj _ (natDegree_N3 n x),
    comp_eq hx hx1 hj _ (natDegree_N4 n x)]
  have h1 := PowerSeries.mul_inv_cancel _ hc
  linear_combination (((Tsub x j : ℝ[X]) : PowerSeries ℝ) ^ n *
    (Ef n x j (wt n x (N1 n x)) * Ef n x j (wt n x (N1 n x)) * Ef n x j (wt n x (N3 n x)) *
      Ef n x j (wt n x (N4 n x)))) * h1

/-- `E(N)` is `SerInt` when all weights of `N` are `LaurentInt`. -/
theorem serInt_Ef {n j : ℕ} (hj : j ≤ n) (N : ℝ → ℝ[X])
    (hN : ∀ j' ≤ n, LaurentInt (fun x => wt n x (N x) j')) :
    SerInt n (fun x => Ef n x j (wt n x (N x))) := by
  refine ((SerInt.C (hN j hj)).add (SerInt.sum ((range (n + 1)).erase j)
    (F := fun j' x => PowerSeries.C (wt n x (N x) j') * geom (αf x j j') (βf x j j'))
    fun j' hj' => ?_)).congr fun x _ _ => rfl
  obtain ⟨hne, hj'r⟩ := mem_erase.1 hj'
  have hj'n : j' ≤ n := Nat.lt_succ_iff.1 (mem_range.1 hj'r)
  exact (SerInt.C (hN j' hj'n)).mul (SerInt.geom (α := fun x => αf x j j')
    (β := fun x => βf x j j') ((LaurentInt.pow_id j').mul (LaurentInt.inv_pow_id j))
    (dn_div_ratio n j' j hj'n hj hne))

/-- PROOF_T1 Lemma 3 in series form: `d_n^K [u^K] Gser` is `LaurentInt` for every `K`. -/
theorem serInt_Gser {n j : ℕ} (hj : j ∈ range (n + 1)) : SerInt n (fun x => Gser n x j) := by
  have hjn : j ≤ n := Nat.lt_succ_iff.1 (mem_range.1 hj)
  have hT : SerInt n (fun x => ((Tsub x j : ℝ[X]) : PowerSeries ℝ)) :=
    ((SerInt.C (LaurentInt.inv_pow_id j)).mul (SerInt.one.sub SerInt.X)).congr fun x _ _ => by
      simp [Tsub]
  have h1 := serInt_Ef hjn (N1 n) fun j' h => wt_N1_laurent h
  have h3 := serInt_Ef hjn (N3 n) fun j' h => wt_N3_laurent h
  have h4 := serInt_Ef hjn (N4 n) fun j' h => wt_N4_laurent h
  exact ((hT.pow n).mul (((h1.mul h1).mul h3).mul h4)).congr fun x hx hx1 =>
    (Gser_eq hx hx1 hj).symm

end QZeta3.Denom
