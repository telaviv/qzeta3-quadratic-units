# √d·ζ_q(3) is irrational at real quadratic units: a Lean 4 formalisation

Lean 4 + Mathlib (v4.35.0) proof of Theorem T1 of `handoff/fibzeta/many/PROOF_T1.md` and its corollary.

* **T1.** Let q be a real quadratic unit of norm +1 with 0 < |q| < 1, and let ℚ(q) = ℚ(√d). Then
  √d·ζ_q(3) ∉ ℚ, where ζ_q(3) = Σ_{m≥1} m² qᵐ/(1 − qᵐ). In Lean this is `QZeta3.irrational_sqrt_mul_zetaq3`, with
  the hypotheses q + q⁻¹ = s ∈ ℤ and d(s² − 4) a square.
* **Corollary.** For every quadratic-unit Lucas sequence U (U_{m+2} = aU_{m+1} + EU_m with E = 1, a ≥ 1, or
  E = −1, a ≥ 3) and ε = (a + √(a²+4E))/2, the sum Σ_{m≥1} m²(U_{m+1}/U_m − ε) is irrational. In Lean this is
  `QZeta3.irrational_lucas_sum`. The Fibonacci case Σ m²(F_{m+1}/F_m − φ) ∉ ℚ is `QZeta3.irrational_fib_sum`.

Only the standard axioms are used (`Axioms.lean`). What a reader has to trust is in `TRUST.md`.

## Build
```
lake exe cache get              # Mathlib oleans (in this checkout .lake/packages is a junction to a shared copy)
LEAN_NUM_THREADS=4 lake build
lake env lean Axioms.lean
```

## The proof
It follows PROOF_T1, case A = 4, r = 1, with the very-well-poised q-series of Krattenthaler–Rivoal–Zudilin.
* **The linear form.** S_n = Σ_{k≥1} R_n(q^k) − Σ_{k≥1} R_n(q^{−n−k}) satisfies S_n = P₀ + P₃ ζ_q(3).
* **Reciprocity.** Under q ↦ 1/q, P₃ is invariant and P₀ is anti-invariant, up to the factor q^{−n}.
* **The norm argument.** At a unit q with σq = 1/q, Galois conjugation of d_n⁴·b(s²−4)·S_n gives −q^{−n}σ(d_n)⁴ times
  the same S_n. So the norm is ≈ |N d_n|⁴|S_n|², which is less than 1 for large n.

| Lean | PROOF_T1 | file |
|---|---|---|
| `PFIdentity` | (2.1), partial fractions | `QZeta3/PartialFrac/` |
| `Expansion` | Lemma 4 (bilateral expansion) | `QZeta3/Expand/` |
| `Recip` | Lemma 2 and its Corollary, Lemma 5 | `QZeta3/Reciprocity/` |
| `Integrality` | Lemma 3 and §7 denominators | `QZeta3/Denom/` |
| `SizeBound` | Lemmas 1 and 6 | `QZeta3/Size/` |
| `CostBound` | Lemma 7 (weak form, below) | `QZeta3/Cost/` |
| `irrational_sub_inv_mul_zetaq3_of` | §7 (norm argument) | `QZeta3/Main.lean` |
| corollary algebra | §0 Corollary | `QZeta3/Corollary.lean`, `QZeta3/Reduction.lean` |

Each folder has a README that maps its lemmas to proof steps.

**Deviations from PROOF_T1.**
* **Lemma 7 is used in a weak form.** The proof only needs Σ_{ℓ≤n} φ(ℓ) ≤ c·n² for some c < 1/2. The Lean proof
  uses c = 3/8, from a sieve at 2 (φ(2m) ≤ m), instead of the Mertens asymptotic 3/π², which Mathlib lacks. The norm
  bracket becomes 4·3/8 − 2 = −1/2 instead of 12/π² − 2.
* **No number fields.** √d is replaced by θ = q − q⁻¹ (PROOF_T1 Remark 2), σ by evaluation of integer Laurent
  polynomials at q⁻¹, and the norm by p(q)·p(q⁻¹) ∈ ℤ.
* **Partial-fraction coefficients.** They are *defined* as coefficients of the power-series expansion of u⁴R_n at
  each pole. This makes the reciprocity c_{s,j}(1/q) = q^{−n}c_{s,n−j}(q) a direct consequence of Lemma 2.

## Layout
* `QZeta3/Defs.lean`, `QZeta3/Statements.lean`: the frozen definitions and ingredient statements.
* Worker folders: one per ingredient (see the table).
* `QZeta3/Final.lean`: the top file.
* `scripts/check_frozen.py`: exact and numerical checks of the frozen statements; per-area checks are in `scripts/<area>/`.
* `FIDELITY.md`: the blind back-translation of the final statements.
* `STATEMENT_REVIEW.md`: notes for the owner's review of the statements.

License Apache-2.0 (`LICENSE`, `NOTICE`).
