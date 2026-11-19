# lean_qzeta3 workers: shared rules (2026-11-18)

**Goal.** A Lean 4 + Mathlib (v4.35.0) proof of Theorem T1: for real `q` with `0 < |q| < 1` and
`q + q⁻¹ ∈ ℤ` (a real quadratic unit of norm +1), `(q − q⁻¹)·ζ_q(3) ∉ ℚ`, where
`ζ_q(3) = Σ m² q^m/(1 − q^m)`. Only standard axioms are allowed. The written proof is
`C:\Users\Shawn Krisman\math\handoff\fibzeta\many\PROOF_T1.md` (case A = 4, r = 1, so e = k = n);
its referee report is `REFEREE_T1.md` in the same folder. **Read PROOF_T1 §§1–7 first.**

## Architecture (fixed)
* **`QZeta3/Defs.lean`**: all definitions. Generic over a field `𝕜`: `qPoch`, `Rfun`, `qPochPoly`, `Npoly`,
  `Tsub`, `Dother`, `Gser` (a `PowerSeries`), `cc`, `P3`, `Wf`, `P0`. Real-valued: `dn`, `Sn`, `zetaq3`,
  `LaurentInt`. **Read it first. Never edit it.**
  - The partial-fraction coefficient `cc n q s j` is *defined* as `[u^{4−s}]` of the power series
    `Gser n q j = N(q^{−j}(1−u)) · (∏_{j'≠j} (1 − q^{j'}·q^{−j}(1−u))⁴)⁻¹`, i.e. the expansion of
    `u⁴ R_n(T)` at the pole `T = q^{−j}` in `u = 1 − q^j T`.
* **`QZeta3/Statements.lean`**: the frozen ingredients `PFIdentity`, `Expansion`, `Recip`, `Integrality`,
  `SizeBound`, `CostBound`. **Never edit it.**
* **`QZeta3/Main.lean`, `QZeta3/Final.lean`**: the coordinator's files (assembly, the norm argument, the
  corollary). Done or in progress; do not touch them.
* `scripts/check_frozen.py` checks every frozen statement exactly at q = 2/7 and q = 1/p (PF identity,
  Σc = 0, reciprocity, denominators), and numerically at q = ±φ⁻² (expansion, size). Reuse its code for
  your own numerical tests.

**Theorem each worker must prove**, with exactly this signature, in `QZeta3/<Area>/Top.lean`
(namespace `QZeta3.<Area>`):

| worker | folder | theorem |
|---|---|---|
| pf | `QZeta3/PartialFrac/` | `theorem pfIdentity : PFIdentity` |
| expand | `QZeta3/Expand/` | `theorem expansion (hpf : PFIdentity) : Expansion` |
| recip | `QZeta3/Reciprocity/` | `theorem recip (hpf : PFIdentity) : Recip` |
| denom | `QZeta3/Denom/` | `theorem integrality : Integrality` |
| size | `QZeta3/Size/` | `theorem sizeBound : SizeBound` |
| cost | `QZeta3/Cost/` | `theorem costBound : CostBound` |

`expand` and `recip` may use `PFIdentity` as a hypothesis (for example `Σ_{s,j} c_{s,j} = R_n(0) = 0`, from
`PFIdentity` at `T = 0`). If a frozen statement is false or not provable as stated, **stop and report**;
do not change it. Your own helper lemmas and definitions go in your folder.

## Where you work
* Your own git worktree `C:\Users\Shawn Krisman\math\lean_qzeta3_wt\<name>`, on branch `w-<name>`. Work only
  there; never touch `C:\Users\Shawn Krisman\math\lean_qzeta3` (the main checkout) or another worker's worktree.
* `.lake/packages` in your worktree is a junction to `lean_chi2/.lake/packages` (Mathlib). Never delete it, never
  run `lake clean`, `lake update` or `lake exe cache get`, and never delete a worktree folder recursively.

## Building
* Use `LEAN_NUM_THREADS=4`. Single module: `LEAN_NUM_THREADS=4 lake build QZeta3.<Area>.<File>`. For quick
  iteration use `lake env lean QZeta3/<Area>/X.lean` once its imports are built. Mathlib is already built.
* Six workers share a 32 GB machine: run **one** Lean process at a time. Commands that may run longer than about
  2 min go in the background (`run_in_background`), and you wait for the notification. Never kill processes by
  name or guessed PID.
* Keep files small (≤ about 400 lines). Import `QZeta3.Statements` (which imports `QZeta3.Defs`).

## Deliverable
* No `sorry`, `axiom`, `native_decide` or `implemented_by`. `decide +kernel` and `norm_num` are fine. Check
  `#print axioms` in a scratch file that you do not commit: the output must be only `propext, Classical.choice,
  Quot.sound`.
* Commit on your branch (`git add` only your files). The message ends with
  `Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>`. Never merge, rebase or push. Commit at every major
  milestone.
* Test new intermediate statements numerically (Python; exact `fractions.Fraction` where a claim depends on it)
  before proving them. Put the scripts in `scripts/<area>/`.
* Leave a short `QZeta3/<Area>/README.md` mapping your theorems to PROOF_T1 steps.
* Final report (your last message): branch, commit hash, theorem names, files, any added hypothesis (there should be
  none), and build time.
