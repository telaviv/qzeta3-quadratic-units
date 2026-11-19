# Fidelity of the frozen statements

## 1. Blind back-translation, same-family (Claude) reviewer — 2026-11-18
* **Packet.** The reviewer got only the bare Lean source of `zetaq3`, `lucasU`, `epsU` and the five final theorems
  (`Final.lean` statements, proofs `sorry`). Comments, docstrings, PROOF_T1 and the intended prose were all removed.
  It was told not to infer intent from names. It could read Mathlib sources to confirm definitions.
* **Reviewer's translation, in summary.**
  - **Thm 1.** For real q ≠ 0 with |q| < 1 and q + 1/q = s ∈ ℤ, (q − 1/q)·ζ_q(3) ∉ ℚ, where ζ_q(3) = Σ m²qᵐ/(1−qᵐ).
    - The reviewer worked out that the hypotheses force |s| ≥ 3 and q = (s − sgn(s)√(s²−4))/2. So the statement says
      "√(s²−4)·ζ_q(3) ∉ ℚ for every real quadratic unit of norm +1 with |q| < 1".
    - Not vacuous: s = 3 gives q = (3−√5)/2.
    - `hq0` is needed. Without it, q = 0 gives a rational junk value.
  - **Thm 2.** Thm 1's hypotheses plus d > 0 with d(s²−4) a square in ℤ give √d·ζ_q(3) ∉ ℚ. Satisfiable (s = 3, d = 5).
    It is a nonzero rational multiple of Thm 1, and √d is the true square root.
  - **Thm 3.** For (E = 1, a ≥ 1) or (E = −1, a ≥ 3): Σ m²(U_{m+1}/U_m − ε) ∉ ℚ.
    - No junk values: a²+4E ≥ 5, U_m ≥ 1 for m ≥ 1, and the m = 0 term is killed by m².
    - The excluded cases (a = 2 or a = 1 with E = −1) are exactly the degenerate ones.
    - The sum is genuine and equals √(a²+4E)·ζ_q(3) with q = ε̄/ε.
  - **Thm 4.** The a = E = 1 (Fibonacci) instance, equal to √5·ζ_{−φ⁻²}(3).
  - **Thm 5.** The ζ_q series is summable for |q| < 1, so `zetaq3` is not the junk value 0.
  - **Flags.** None vacuous, none true only through a junk value.
  - **Missing from the packet.** The intended statements; summability of the Lucas series; `lucasU 1 1 = fib`; an
    axiom report.
* **Comparison with PROOF_T1 Theorem T1 and the Corollary** (done only after the reply).
  - T1 assumes K = ℚ(√d) real quadratic and q ∈ O_K^× with N(q) = +1, 0 < |q| < 1. Then σq = 1/q, so
    s = q + q⁻¹ = Tr q ∈ ℤ and q ≠ 0. Also K = ℚ(q) = ℚ(√(s²−4)), so d(s²−4) is a rational square, hence an
    integer square, and d > 0.
  - Conversely, the reviewer's translation shows the Lean hypotheses describe exactly such q (with d not required to
    be squarefree, which is more general).
  - The conclusion √d·ζ_q(3) ∉ ℚ, with ζ_q(3) = Σ m²qᵐ/(1−qᵐ), matches.
  - The corollary parametrises the quadratic units ε > 1 as (trace a, norm −E) and matches PROOF_T1's Corollary,
    including Fibonacci.
* **Verdict: no mismatch.** The packet's missing items are answered in `QZeta3/Reduction.lean`:
  `lucasU_one_one` (U for a = E = 1 equals fib), `summable_lucas` (summability of the Lucas series) and
  `summable_zetaq3`. The axiom report will be in `Axioms.lean`.
