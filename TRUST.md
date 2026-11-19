# What you have to trust

## Axioms

`lake env lean Axioms.lean` prints, for every final theorem (full output: `scripts/axioms.txt`),

```
'QZeta3.irrational_sqrt_mul_zetaq3' depends on axioms: [propext, Classical.choice, Quot.sound]
'QZeta3.irrational_sub_inv_mul_zetaq3' depends on axioms: [propext, Classical.choice, Quot.sound]
'QZeta3.irrational_lucas_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'QZeta3.irrational_fib_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'QZeta3.summable_zetaq3' depends on axioms: [propext, Classical.choice, Quot.sound]
'QZeta3.summable_lucas' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are Lean's three standard axioms, the ones Mathlib uses. The project has no `sorry`, no `axiom` declaration, no
`native_decide` and no `implemented_by`, so nothing relies on the compiler.

## The statement

The kernel checks the proof; it cannot check that the statement means what we claim. Read `QZeta3/Final.lean` (the
four theorem statements) and three definitions in `QZeta3/Defs.lean`:

```lean
noncomputable def zetaq3 (q : ℝ) : ℝ := ∑' m : ℕ, (m : ℝ) ^ 2 * q ^ m / (1 - q ^ m)

def lucasU (a : ℕ) (E : ℤ) : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | (m + 2) => a * lucasU a E (m + 1) + E * lucasU a E m

noncomputable def epsU (a : ℕ) (E : ℤ) : ℝ := (a + Real.sqrt ((a : ℝ) ^ 2 + 4 * E)) / 2
```

* `zetaq3 q = Σ_{m≥1} m² qᵐ/(1 − qᵐ)`. The m = 0 term is `0·1/0 = 0` in Lean. A divergent `tsum` would have the
  junk value 0, which is rational, so no theorem below can hold for a degenerate reason. `summable_zetaq3` and
  `summable_lucas` prove convergence anyway.
* `irrational_sqrt_mul_zetaq3`: hypotheses `q ≠ 0`, `|q| < 1`, `q + q⁻¹ = s ∈ ℤ`, `d > 0`, `d(s² − 4)` a square.
  - These hypotheses say exactly that q is a real quadratic unit of norm +1 with 0 < |q| < 1 (|s| ≥ 3 is forced)
    and that ℚ(q) = ℚ(√d). So the theorem is PROOF_T1's Theorem T1, with d not required to be squarefree.
  - `irrational_sub_inv_mul_zetaq3` is the same statement with q − q⁻¹ = ±√(s² − 4) in place of √d.
* `irrational_lucas_sum`: `(E = 1 ∧ a ≥ 1) ∨ (E = −1 ∧ a ≥ 3)` are exactly the real quadratic units ε > 1 (trace a,
  norm −E). `irrational_fib_sum` is a = E = 1, with `Nat.fib` and Mathlib's `Real.goldenRatio`.

A blind back-translation of these declarations (reviewer saw only the Lean source, not the intended statement) is
recorded in `FIDELITY.md`; it found no mismatch with PROOF_T1.

## What the proof does not trust

The six ingredients (`QZeta3/Statements.lean`) and the internal construction (`Rfun`, `cc`, `P0`, `P3`, `dn`, `Sn` in
`QZeta3/Defs.lean`) need not be read: they are proved, and the kernel checks that the final theorems follow from
them. Reading them is only needed to see that the formal proof follows PROOF_T1.
