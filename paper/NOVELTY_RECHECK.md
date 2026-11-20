# Novelty re-run for the T1 paper (2026-11-19, ~16:00 PST)

A delta check on top of `handoff/fibzeta/many/NOVELTY_2.md` (same day, full search). Raw output was kept in the session
scratchpad only.

| Source | Query | Result |
|---|---|---|
| Hexagon API | `q=` Lambert, Pisot, q-zeta, zeta_q, quadratic unit, Salem, golden ratio, Lucas; plus the 60 newest records (up to 2611.00673) | Nothing new since NOVELTY_2. The relevant records are still 2611.00623 (Z(b) ∉ ℚ(b), Pisot/Salem; contains T1), 2611.00638 (height criterion), and 2611.00643 (1, M₁, M₂, M₃ independent over ℚ(b); contains T1). All three are by twinheterodox, AI-generated, and not checked in Lean. The abstract of 00623 confirms the hypothesis quoted in the paper: every conjugate outside the closed unit disk lies in {b, b̄}. |
| GitHub | `gh repo list twinheterodox`; `gh search repos` for q-zeta irrational, lambert series irrational, zeta_q, weight-three lambert, quadratic unit irrational, golden ratio lambert | algebraic-base-lambert-values: last push still 2026-11-19 04:43 UTC. The only other new repo is weighted-even-lucas-reciprocals (2611.00639, q-β, not T1). Otherwise only our telaviv/chi2 repo. |
| Zenodo API | "q-zeta"; "Lambert series" AND irrational*; "Lambert sum"; Pisot AND Lambert; "quadratic unit" AND irrational* | Noise only, no odd q-zeta value at algebraic q. |
| arXiv API | abs: "Lambert series" AND irrationality; "q-zeta" AND irrational; Pisot AND Lambert; "basic hypergeometric" AND irrationality | Nothing new: Ahmes series (2608), an older 2024 paper, and empty results. |

**Verdict:** unchanged from NOVELTY_2.
* T1 is concurrent with, and contained in, the claims of 2611.00623 and 2611.00643.
* What remains ours is the independent method, the Lean proof, and the explicit Lucas form.
* The paper claims no priority for T1. It cites both preprints in the introduction.
