# lean_qzeta3 notes

Lean 4 + Mathlib (v4.35.0) formalisation of **Theorem T1**: √d·ζ_q(3) ∉ ℚ for a real quadratic unit q of norm +1 with
0 < |q| < 1. It also covers the Lucas corollary Σ m²(U_{m+1}/U_m − ε) ∉ ℚ, including Fibonacci.
* Source proof: `../handoff/fibzeta/many/PROOF_T1.md`, refereed in `REFEREE_T1.md`.
* Started and completed 2026-11-18/19 in one session. Library `QZeta3`, namespace `QZeta3`. Git repo on branch
  `main`, not pushed; the owner pushes.
* `.lake/packages` is a Windows junction to `../lean_chi2/.lake/packages`. Don't delete it.
* Build: `LEAN_NUM_THREADS=4 lake build` takes about 4.5 min. Axioms: `lake env lean Axioms.lean`, output saved in
  `scripts/axioms.txt`.
* Final theorems are in `QZeta3/Final.lean`: `irrational_sqrt_mul_zetaq3`, `irrational_sub_inv_mul_zetaq3`,
  `irrational_lucas_sum`, `irrational_fib_sum`, `summable_zetaq3`, `summable_lucas`.
* Architecture: frozen `Defs.lean` and `Statements.lean`, with six ingredients proved by six parallel workers
  (branches `w-{pf,expand,recip,denom,size,cost}`, merged; worktrees removed). `Main.lean` holds the norm argument,
  `Corollary.lean` and `Reduction.lean` the corollaries. Rules are in `WORKERS.md`, proof outlines in
  `WORKER_BRIEFS.md`.
* Lemma 7 uses the weak form Σφ(ℓ) ≤ 3(n+1)²/8 (sieve at 2), not 3/π². Any constant below 1/2 suffices.
* Fidelity: a blind back-translation (`FIDELITY.md`) found no mismatch. Owner review of the statements:
  `STATEMENT_REVIEW.md`, approved by the owner on 2026-11-19 with no changes.
* Machine note: a cold `import Mathlib` was very slow on 2026-11-18 (over 5 min); warm it is about 1 min.
