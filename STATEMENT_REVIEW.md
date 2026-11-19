# Frozen statement for owner review (2026-11-18)

**Status: approved by the owner on 2026-11-19** ("Approve statements"), with no changes. The approved statements are
the four theorems below, as they stand in `QZeta3/Final.lean` at commit 6318359.

These are the only Lean statements whose meaning the kernel cannot check for you. Everything else (the internal
construction `Rfun`, `cc`, `P0`, `P3`, `dn`, `Sn` and the six ingredients) is checked by the kernel against these.
Files: `QZeta3/Final.lean` (theorems), `QZeta3/Defs.lean` (the three definitions they use).

## Definitions used in the statements
```lean
noncomputable def zetaq3 (q : ℝ) : ℝ := ∑' m : ℕ, (m : ℝ) ^ 2 * q ^ m / (1 - q ^ m)
-- m = 0 term is 0·1/0 = 0 in Lean; `summable_zetaq3` proves the series converges for |q| < 1.

def lucasU (a : ℕ) (E : ℤ) : ℕ → ℤ        -- U₀ = 0, U₁ = 1, U_{m+2} = a U_{m+1} + E U_m
noncomputable def epsU (a : ℕ) (E : ℤ) : ℝ := (a + Real.sqrt ((a : ℝ) ^ 2 + 4 * E)) / 2
```

## Theorem T1
```lean
theorem irrational_sqrt_mul_zetaq3 {q : ℝ} {s : ℤ} (hq0 : q ≠ 0) (hq1 : |q| < 1)
    (hs : q + q⁻¹ = s) {d : ℕ} (hd : 0 < d) (hsq : IsSquare ((d : ℤ) * (s ^ 2 - 4))) :
    Irrational (Real.sqrt d * zetaq3 q)

theorem irrational_sub_inv_mul_zetaq3 {q : ℝ} {s : ℤ} (hq0 : q ≠ 0) (hq1 : |q| < 1)
    (hs : q + q⁻¹ = s) : Irrational ((q - q⁻¹) * zetaq3 q)
```
Why the first one is T1:
* A real q is a unit of norm +1 in a real quadratic field K exactly when its trace s = q + q⁻¹ is an integer and
  q ∉ ℚ. Here 0 < |q| < 1 forces |s| > 2, so s² − 4 is not a square and q ∉ ℚ holds automatically.
* Then K = ℚ(q) = ℚ(√(s² − 4)), and K = ℚ(√d) exactly when d(s² − 4) is a square.
* The Lean form is slightly more general than T1: it allows any d > 0 with d(s² − 4) a square, not only squarefree d.

## Corollary
```lean
theorem irrational_lucas_sum {a : ℕ} {E : ℤ} (h : (E = 1 ∧ 1 ≤ a) ∨ (E = -1 ∧ 3 ≤ a)) :
    Irrational (∑' m : ℕ, (m : ℝ) ^ 2 * ((lucasU a E (m + 1) : ℝ) / lucasU a E m - epsU a E))

theorem irrational_fib_sum :
    Irrational (∑' m : ℕ, (m : ℝ) ^ 2 * ((Nat.fib (m + 1) : ℝ) / Nat.fib m - Real.goldenRatio))
```
* The admissible (a, E) are exactly the real quadratic units ε > 1: trace a, norm −E.
  - E = 1, a ≥ 1 gives norm −1 (PROOF_T1's t = a with N(ε) = −1).
  - E = −1, a ≥ 3 gives norm +1.
* The m = 0 term is 0 in Lean (factor 0²). The proof shows the summand equals √(a² + 4E)·m²qᵐ/(1 − qᵐ) termwise,
  with q = ε̄/ε.

## Design choices worth a look
* T1 is stated without Mathlib number fields: q real, q + q⁻¹ ∈ ℤ. The conjugation σ is evaluation of integer
  Laurent polynomials at q⁻¹, and the norm is p(q)·p(q⁻¹) ∈ ℤ. This is PROOF_T1 §7 verbatim, with θ = q − q⁻¹ in the
  role of √d (Remark 2).
* Lemma 7 is formalised in a weak form. Instead of Σ_{ℓ≤n} φ(ℓ) = 3n²/π² + O(n log n), it uses
  Σ_{ℓ≤n} φ(ℓ) ≤ 3(n+1)²/8, a sieve at 2. The norm bracket becomes 4·(3/8) − 2 = −1/2 instead of 12/π² − 2.
  PROOF_T1 says "the constant 3/π² is essential", but any constant below 1/2 suffices. So the Mertens asymptotic
  (absent from Mathlib) is not needed.
