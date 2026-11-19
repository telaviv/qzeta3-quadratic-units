# Area briefs for the lean_qzeta3 workers (2026-11-18)

Each worker's prompt points here and to `WORKERS.md`. These are proof outlines, not frozen statements;
any route that proves the frozen theorem is fine.

## pf — `QZeta3.PartialFrac.pfIdentity : PFIdentity`
Partial fractions (2.1). Fix n ≥ 1 and real q (q ≠ 0, |q| ≠ 1). Put D(T) = ∏_{j≤n} (1 − q^j T)⁴ (= `qPoch T q (n+1) ^ 4`) and
  H(T) = Npoly(T) − Σ_{j,s} c_{s,j} (1 − q^j T)^{4−s} ∏_{j'≠j} (1 − q^{j'} T)⁴  ∈ ℝ[T].
* deg Npoly = 3n < 4(n+1), so deg H < 4(n+1) = deg D.
* For each j, `H.comp (Tsub q j)` is divisible by `X⁴`. In 𝕜⟦u⟧: `Npoly.comp (Tsub q j) = Gser · Dother`. The j-term is
  (Σ_s c_{s,j} u^{4−s}) · Dother, because (1 − q^j T) ∘ Tsub = u. Every j₂ ≠ j term contains (1 − q^j T)⁴ ↦ u⁴. So
  H ∘ Tsub ≡ (Gser − Σ_{s=1}^{4} c_{s,j} u^{4−s}) · Dother ≡ 0 mod u⁴, since c_{s,j} = [u^{4−s}] Gser.
  Pull this back with T ↦ u = 1 − q^j T (`Tsub` is invertible under `comp`), to get (1 − q^j T)⁴ ∣ H.
* The (1 − q^j T)⁴ are pairwise coprime (distinct roots q^{−j}, since q is not a root of unity), so D ∣ H; by degree, H = 0.
* Evaluate at T, use `eval (Npoly) T = numerator of Rfun`, and divide by D(T) ≠ 0.
Useful Mathlib: `Polynomial.coeToPowerSeries`, `PowerSeries.coeff`, `PowerSeries.mul_inv_cancel`
(constant coefficient of `Dother` is ∏ (1 − q^{j'−j})⁴ ≠ 0), `Polynomial.X_pow_dvd_iff`, `IsCoprime`, `Finset.prod_dvd_of_coprime`,
`Polynomial.eq_zero_of_dvd_of_degree_lt`.

## expand — `QZeta3.Expand.expansion (hpf : PFIdentity) : Expansion`
Lemma 4 at A = 4. Fix n ≥ 1 and 0 < |q| < 1.
* Σ_{s,j} c_{s,j} = 0: use `hpf` at T = 0, where Rfun n q 0 = 0 because of the factor Tⁿ.
* From `hpf` at T = q^k (k ≥ 1) and at T = q^{−n−k}: R(q^k) = Σ c_{s,j} [(1 − q^{j+k})^{−s} − 1] and
  R(q^{−n−k}) = Σ c_{s,j} (1 − q^{j−n−k})^{−s}. Sum over k; each inner series is absolutely summable.
* With F_s = Σ_{m≥1} [(1 − q^m)^{−s} − 1] and G_s = Σ_{m≥1} (1 − q^{−m})^{−s} one gets
  Sn = Σ_{s,j} c_{s,j} (F_s − G_s) + P0 (this is the definition of `Wf`: the finite pieces m ≤ j and m ≤ n−j).
* Termwise in y = q^m: (1 − y)^{−s} − 1 − (1 − 1/y)^{−s} = (1 − (−y)^s)/(1 − y)^s − 1, which is
  2y/(1−y) for s = 1, 2, and 2y/(1−y) + s'·y(1+y)/(1−y)³ with s' = 1 for s = 3 and s' = 2 for s = 4.
  Check: Σ_i (C_s(i) + C_s(−i)) y^i with C_s(x) = binom(x+s−1, s−1) gives 2, 2, i² + 2, 2i² + 2.
* Σ_m q^m(1+q^m)/(1−q^m)³ = Σ_m Σ_i i² q^{mi} = Σ_i i² q^i/(1 − q^i) = ζ_q(3) (swap an absolutely convergent double sum).
  The Lambert part 2 Σ_m q^m/(1−q^m) is multiplied by Σc = 0.
* Hence Σ_{s,j} c_{s,j}(F_s − G_s) = Σ_j (c_{3,j} + 2c_{4,j}) ζ_q(3) = P3 ζ_q(3).
Note: `Sn` and `zetaq3` are `tsum`s; prove `HasSum`/`Summable` for every series you split.

## recip — `QZeta3.Reciprocity.recip (hpf : PFIdentity) : Recip`
Lemma 2 (coefficient form) and Lemma 5. Fix n ≥ 1, real q ≠ 0 with |q| ≠ 1, and j ≤ n.
* `Dother n q⁻¹ j = Dother n q (n − j)`: reindex j' ↦ n − j'; both are ∏ (1 − q^{j−j'}(1−u))⁴.
* Polynomial identity N(T; 1/q) = q^{−n} N(q^{−n}T; q), in the form
  `(Npoly n q⁻¹).comp (Tsub q⁻¹ j) = C (q^n)⁻¹ * (Npoly n q).comp (Tsub q (n − j))`
  (factor by factor, as in PROOF_T1 Lemma 2; (q^n T; 1/q)_n and (q T; q)_n trade places, and so do
  (q^{−n−1}T; 1/q)_n and (q^{−2n}T; q)_n).
* Hence `Gser n q⁻¹ j = C (q^n)⁻¹ * Gser n q (n − j)` and `cc n q⁻¹ s j = (q^n)⁻¹ * cc n q s (n − j)`.
* `P3`: reindex with `Finset.sum_range_reflect`.
* `Wf n q⁻¹ s (n − j) = −Wf n q s j − n` (PROOF_T1 Lemma 5 proof; note 1 − (q⁻¹)^m and 1 − ((q⁻¹)^m)⁻¹ swap roles).
  Then `P0 n q⁻¹ = −(q^n)⁻¹ P0 n q`, using Σ_{s,j} c_{s,j} = 0 (from `hpf` at T = 0, where Rfun n q 0 = 0).
* `scripts/check_frozen.py` already confirms all of these exactly at q = 2/7.

## denom — `QZeta3.Denom.integrality : Integrality`
Lemma 3 and the §7 consequences. This is the biggest algebraic area.
* `LaurentInt` closure: constants (ℤ), `x`, `x⁻¹`, +, −, ×, finite sums and products, powers.
* For 1 ≤ m ≤ n: `x ↦ dn n x / (1 − x^m)` is LaurentInt (in fact a polynomial), because
  X^m − 1 = ∏_{ℓ∣m} Φ_ℓ (`prod_cyclotomic_eq_X_pow_sub_one`) divides ∏_{ℓ≤n} Φ_ℓ. The same holds for 1 − x^{−m}.
* `dn^s · Wf n x s j` is LaurentInt for 1 ≤ s ≤ 4.
* Main claim: `dn^{4−s} · cc n x s j` is LaurentInt. Write `Gser = Tser(u)ⁿ · ∏_{i=1}^{4} g_i(u)`, where Tser = q^{−j}(1−u),
  g_i = N_i(T(u)) · (∏_{j'≠j} (1 − q^{j'}T(u)))⁻¹ and N_1 = N_2 = (q;q)_n, N_3 = `qPochPoly (q^n)⁻¹ q n`,
  N_4 = `qPochPoly (q^(n+1)) q n`.
  - Simple partial fractions: N_i(T) = Σ_{j'} a_{i,j'} ∏_{j''≠j'} (1 − q^{j''}T). Both sides have degree ≤ n and agree
    at the n+1 points q^{−j'} (`Polynomial.eq_of_degree_sub_lt_of_eval_finset_eq`). Here
    a_{i,j'} = N_i(q^{−j'}) / ∏_{j''≠j'} (1 − q^{j''−j'}).
  - a_{i,j'} is LaurentInt: up to ±q^{(…)} it is a Gaussian binomial (type 1), or a product of two Gaussian binomials
    (types 3 and 4: [n+j', n]·[n, j'] and [2n−j', n]·[n, j']); see PROOF_T1 Lemma 3. Gaussian binomials in ℤ[X] via the
    q-Pascal recursion, with (q;q)_k (q;q)_{n−k} [n,k] = (q;q)_n.
  - Hence g_i = a_{i,j} + u Σ_{j'≠j} a_{i,j'}/(α_{j'} + β_{j'}u), with α = 1 − q^{j'−j} and β = q^{j'−j}. The coefficient of
    u^M (M ≥ 1) is Σ_{j'≠j} a_{i,j'}(−β)^{M−1}/α^M. Each α_{j'} is ± a q-power times (1 − q^{|j'−j|}), so
    dn^M · [u^M] g_i is LaurentInt.
  - [u^{4−s}] of the product is a sum over M_0 + … + M_4 = 4 − s, so dn^{4−s} c_{s,j} is LaurentInt.
* Conclude: dn⁴·P0 = −Σ (dn^{4−s} c_{s,j})(dn^s W_{s,j}) and dn⁴·P3 = dn³·Σ_j (dn c_{3,j} + 2 dn c_{4,j}).
Uniformity: LaurentInt needs one polynomial for all x. So prove, for every admissible x, that `cc n x s j` equals an
explicit expression built from x by ring operations and division by (1 − x^m), 1 ≤ m ≤ n; then apply the closure lemmas.

## size — `QZeta3.Size.sizeBound : SizeBound`
Lemmas 1 and 6, with r = 1, e = n. Fix 0 < |q| < 1 and put κ = |q|.
* Lemma 1 at T = q^{k+1}: `Rfun n q (q^(n+k+1))⁻¹ = q^(2n + 4(k+1)) * Rfun n q (q^(k+1))` (factor by factor).
* R(q^k) = 0 for 1 ≤ k ≤ n (the factor (q^{k−n}; q)_n contains 1 − q⁰).
* For k ≥ n+1, every Pochhammer in R(q^k) has base exponent ≥ 1. With c₋ = ∏(1 − κ^i) > 0 and c₊ = ∏(1 + κ^i):
  C⁻¹ κ^{kn} ≤ |R(q^k)| ≤ C κ^{kn}, where C = (c₊/c₋)^8. Any finite-product version with uniform constants is fine.
* Sn = Σ_{k≥n+1} (1 − q^{2n+4k}) R(q^k). The main term is k = n+1 and the tail is geometric, so for large n
  Sn ≠ 0 and |Sn| ≤ C' κ^{n(n+1)}.

## cost — `QZeta3.Cost.costBound : CostBound`
Lemma 7, weak form. Fix 0 < |q| < 1 and put κ = |q|.
* For ℓ ≥ 1: |Φ_ℓ(q) Φ_ℓ(1/q)| = κ^{−φ(ℓ)} ∏_{a∣ℓ} |1 − q^a|^{2μ(ℓ/a)}. Use the Möbius product
  Φ_ℓ(x) = ∏_{a∣ℓ} (x^a − 1)^{μ(ℓ/a)} at x = q and x = 1/q (`Polynomial.cyclotomic_eq_prod_X_pow_sub_one_pow_moebius`,
  or `ArithmeticFunction.prod_eq_iff_prod_pow_moebius_eq_of_nonzero` with `prod_cyclotomic_eq_X_pow_sub_one`), and
  Σ_{a∣ℓ} a μ(ℓ/a) = φ(ℓ). Alternatively use the palindromic identity Φ_ℓ(1/x) = x^{−φ(ℓ)} Φ_ℓ(x) for ℓ ≥ 2.
* Hence |Φ_ℓ(q)Φ_ℓ(1/q)| ≤ B κ^{−φ(ℓ)}, with B = (∏_{a≥1} (1+κ^a)/(1−κ^a))², or any bound uniform in ℓ.
* Σ_{ℓ≤n} φ(ℓ) ≤ 3(n+1)²/8: φ(ℓ) ≤ ℓ always, and φ(2m) ≤ m (only odd residues are coprime to 2m). So
  Σφ ≤ Σ_{odd ℓ≤n} ℓ + Σ_{2m≤n} m ≤ (n+1)²/4 + n(n+2)/8 ≤ 3(n+1)²/8.
* So |dn(q) dn(1/q)|⁸ ≤ B^{8n} κ^{−8Σφ} ≤ (B⁸)ⁿ (κ⁻¹)^{3(n+1)²}.
