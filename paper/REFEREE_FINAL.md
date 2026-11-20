# Final referee report

**Paper:** "Irrationality of odd q-zeta values at real quadratic units" (`paper/main.tex`; I rebuilt it into
`referee_scratch/final/build/`, 18 pp.). **Date:** 2026-11-19.

**Section numbers.** In the compiled paper the many-values section is **§9** (Lemmas 9.1–9.3, Remark 9.4), Related work
is §10 and Formal verification is **§11**. The brief's "Section 8" and "Section 10" mean §9 and §11. All numbers below are
the compiled ones.

## Recommendation

**Accept after minor revision.** Before posting, the two `\TODO{public repository URL}` markers must be filled (point 1).
Everything else is minor or exposition.

## Summary

The paper proves three things.
- Theorem 1.1: a dimension bound dim ≥ 1 + τ(A, r), asymptotically 0.6718√A, for 1 and √d ζ_q(3), …, √d ζ_q(A−1) at a
  real quadratic unit q of norm +1. Corollary 1.2 is the case A = 12.
- Theorem 1.3: √d ζ_q(3) ∉ ℚ, with a separate elementary proof.
- The Lucas and Fibonacci corollaries.

The mechanism is the reciprocity P_l(1/q) = q^{−e}P_l, P_0(1/q) = −q^{−e}P_0 of the KRZ-type coefficients. At such a unit
it makes the trace forms Tr(Δ′P_0) + Σ Tr(Δ′P_l/√d)·√d ζ_q(l) equal to (Δ′ − q^{−e}σΔ′)S_n. Balancing Δ′ by a power of q
then halves the cyclotomic cost at each place.

I read §9 line by line and re-derived every estimate by hand. I recomputed every numerical claim, and rebuilt the forms
exactly in ℚ(√d) at four units (checks listed at the end).

**I found no mathematical error.** The following all hold, both by hand and by computer:
- Lemma 9.1, including the need for the factor (A−1)!: without it integrality fails for every A ≥ 6 I tested.
- Lemma 9.2: every factor bound and the exponent 𝓔(j).
- The exact symmetry σd_n = −q^{−𝒯(n)}d_n.
- The balancing (9.3) and log M_n.
- Lemma 9.3 (a)–(d).
- The application of Nesterenko's criterion: the n² form is KRZ's Prop. 2 verbatim, and FZ Theorem A's hypothesis (N)
  matches.
- The algebra 1 − α/β = 1 + τ, the asymptotic optimisation, admissibility of ⌈t√A⌉ for even A ≥ 6, and 1 + τ(12,2) =
  2.1601.
- The Lucas extension.
- Remark 9.4: 1 + τ = 2δ_KRZ is an exact identity against KRZ's (3.4), δ(12,2) = 1.080059 in KRZ, and the
  unbalanced 0.5398 bound.

§§2–8 are consistent with the restructuring:
- Numbering and cross-references are correct.
- The clean rebuild has no undefined references and no overfull boxes.
- The paper claims no priority for Theorem 1.3.
- It never suggests that Theorem 1.1 is formalised. It says the opposite three times: lines 117, 227 and 622.

**Lean fidelity of §11: faithful.**
- The four quoted statements and the three definitions match `Final.lean` and `Defs.lean` verbatim.
- Every Lean name in §11 and its table exists, with the stated role.
- The six ingredient descriptions match `Statements.lean`.
- Toolchain and Mathlib are v4.35.0, and the sources total about 3,190 lines.
- `Defs.lean` and `Statements.lean` are unchanged since the first commit.
- My axiom rerun gives the three standard axioms for all six theorems.
- `lake build` is up to date and succeeds with no `sorry`.

There are two small factual slips in the chronology sentence (point 2).

## Numbered points

### Must fix before posting

1. **(minor; blocking) Lines 226 and 852: `\TODO{public repository URL}`.** These print in bold in the PDF.
   *Fix:* insert the URL. The preamble comment (line 34) requires every `\TODO` to be resolved before posting.

### Formal verification (§11)

2. **(minor; factual) §11, the paragraph on axioms and freezing (lines 891–894 and 854).**
   - "The four theorem statements above were committed with placeholder proofs before the last three ingredients were
     proved" is not quite right. The statements entered in `9a98dbc` (23:47:09). `CostBound` had already been proved in
     `91754c3` (23:46:49, branch `w-cost`), 20 s earlier. Only `Expansion` (`f09830a`, 23:48:32) and `Integrality`
     (`747472d`, 23:57:15) were proved afterwards. Three ingredients were *merged* afterwards. The statement text is
     indeed unchanged: `git diff 9a98dbc 6318359 -- QZeta3/Final.lean` differs only in imports, proofs, and the removal
     of `summable_zetaq3`, which moved to `Reduction.lean`.
     *Fix:* "…before the last three ingredients were merged (two of them before they were proved)", or "before the last
     two ingredients were proved".
   - "later commits change only documentation and this paper": `paper/` is untracked (`git status`: `?? paper/`). The
     only later commit, `ca3ef6a`, touches `CLAUDE.md` and `STATEMENT_REVIEW.md`.
     *Fix:* commit the paper before posting, or write "later commits change only documentation".
   - Optional repo hygiene, not a paper change: the docstring of `irrational_fib_sum_ing` (`Reduction.lean`, line 105)
     reads "The final estimate: …", which was copied by mistake from `Main.lean`.

### Mathematics and numerics

3. **(minor) Remark after Lemma 9.2 (lines 693–694): the stated reason is inaccurate.** "We include the proof because it
   is needed at real q of both signs" implies that KRZ's Lemma 5 does not cover negative q. In fact KRZ's Lemma 5 (§3.5)
   is stated "pour … q tel que |q| < 1". The real reasons for including the proof are:
   - our R_n is a different rational function (weight T^e, summed bilaterally, no factor q^{−(A−2r)n/4});
   - KRZ give only a limsup, whereas we need an explicit bound for our own c_{s,j}.

   *Fix:* "we include the proof because our c_{s,j} are not those of [KRZ06], and we want an explicit bound."

4. **(minor; numerical) Remark 8.2, "log|P_0|/(n² log(1/|q|)) ∈ [0.91, 0.95] at n = 12 for six values of q".**
   - My values at n = 12 are:

     | q | φ⁻² | −φ⁻² | 2−√3 | −(2−√3) | 3−2√2 | −(3−2√2) | (5−√21)/2 |
     |---|---|---|---|---|---|---|---|
     | ratio | 0.951 | 0.910 | 0.932 | **0.900** | 0.922 | 0.910 | 0.925 |

   - The φ⁻² value matches the author's `measure_sgn1.log` (0.95103). The range is right only for an unnamed choice of six q.

   *Fix:* write "0.90–0.95 for the units we tried", or name the six q.

5. **(minor; numerical wording) Remark 8.1, "oscillates around this value [12/π² − 2 = −0.784]".**
   - My recomputation reproduces the stated ranges: [−0.819, −0.582] at φ⁻², and [−0.840, −0.719] at −φ⁻² for 6 ≤ n ≤ 30.
   - At φ⁻², however, 19 of the 25 values lie above −0.784, with mean −0.741. At −φ⁻² the mean is −0.779.

   *Fix:* "fluctuates in … and approaches this value", or "stays near".

### Introduction and related work

6. **(minor) [UPL] is "claimed" in the introduction (line 82) but "proves" in §10 (line 833).** By the notes
   (`NOVELTY_2.md`), the Lean proof is reported in that repository's `docs/VERIFICATION.md`. We have not checked it.
   *Fix:* in §10, write "claims … with a Lean formalisation of its main theorem (not checked by us)". This also follows
   the project's rule of stating verification status.

7. **(minor) §10, "Concurrent work" (lines 836–838).**
   - (a) "The preprints [Twi26, Twi26b] … build on [UPL]": the notes support this only for [Twi26]. The introduction,
     line 175, correctly says only [Twi26]. *Fix:* "[Twi26] builds on [UPL]".
   - (b) "the linear independence of 1, ζ_q(1), ζ_q(2), ζ_q(3) over ℚ(b)": q is undefined there. *Fix:* write ζ_{1/b}.
     I checked the change of basis from the M_j: M_1 = ζ_{1/b}(1), M_2 = ζ_{1/b}(2) − ζ_{1/b}(1), and
     2M_3 = ζ_{1/b}(3) − 3ζ_{1/b}(2) + 2ζ_{1/b}(1). I also checked ζ_{1/b}(3) = M_1 + 3M_2 + 2M_3.
   - (c) "for Pisot and Salem numbers b" is narrower than the class quoted in the introduction, which includes non-real
     b. *Fix:* "for the class described in the introduction (which contains the Pisot and Salem numbers)".

8. **(exposition) Introduction, lines 213–215: "With the same machine (the series, the denominators and the single-form
   criterion)".**
   - Our series is a variant: weight T^e and summed bilaterally (line 189).
   - The factor-2 comparison holds because the three leading constants are identical: decay r(A−2r)/2, coefficients
     (A+4r²)/8, denominator 3A/π². These are KRZ's points B, C and D.

   *Fix:* "with the same leading constants (decay, coefficient size and denominator, which our series shares with that of
   [KRZ06]) and the same single-form criterion". Remark 9.4 can carry the same wording.

### Exposition and notation

9. **(exposition) Notation clashes in §§3, 7 and 9.**
   - `c_3`, `c_4` (constants of Lemma 9.2) against `c_{3,j}`, `c_{4,j}` (proof of Theorem 1.3). This one is a real
     misreading risk. *Fix:* rename them γ_−, γ_+, or similar.
   - ρ is the Cauchy radius in Lemma 9.2, the block index ρ = 1..r in Lemma 3.2, and ϱ_n in (9.3).
   - c = 1−b−n in Lemma 3.2.
   - w = 1−u against the constant w_0.
   - M is the product index in Lemma 9.2, against M_n.
   - m is the balancing exponent m_n and also the summation index.
   - ℓ is the index of Φ_ℓ, against the forms ℓ_{l,n}.
   - N appears in Lemma 3.2, in Nesterenko's N, and in Nm.
   - P, Q are the Lucas parameters, against P_l and 𝒬. They meet in §8, where the Corollary 1.4 proof follows the
     Theorem 1.3 proof.
   - The weight is called s in the proof of the asymptotic bound ("Σ m^{s−1}…", line 781), clashing with the index s
     and the trace s. *Fix:* use l there.
   - b̄ is a complex conjugate (introduction) but η̄ is a Galois conjugate.

10. **(exposition) §9, choice of d.**
    - The introduction allows any integer d ≥ 1 with K = ℚ(√d). §9 switches to squarefree d only after defining the forms
      ("with d squarefree", line 727), and returns to general d in the last sentence of the proof.
      *Fix:* say at the start of "Balanced trace forms": "Here d is squarefree; the general case follows at the end of the
      proof."
    - "For large n put ϱ_n": m_n is defined for every n, so "for large n" can go.

11. **(exposition) Abstract, "invariant or anti-invariant under q ↦ 1/q".** The invariance holds only up to the factor
    q^{−e}. *Fix:* "invariant or anti-invariant up to a power of q".

## Checks run

All scripts and logs are in `paper/referee_scratch/final/`.

| # | Claim | Script / log | Result |
|---|---|---|---|
| 1 | Lemmas 2.1 and 2.2, (3.1) with Σc = 0, Cor. 3.1, Lemma 3.2, Lemma 5.1, Q_0 = 0, Lemma 9.1, σd_n = −q^{−𝒯(n)}d_n | `f_sym.py` / `f_sym.log` | Exact in ℚ(q, T) for (A,r,n) = (4,1,1–3), (6,1,2), (6,2,2), (8,1,1), (8,2,2), (8,3,1), (10,2,1), (12,2,1): **all pass**. The negative control (c_{1,j} without d_n) fails as it should |
| 2 | Is (A−1)! needed in Lemma 9.1? Does d_n^{A−1}P_0 suffice (Remark 9.4)? | `f_sym.log` | (A−1)! is needed for every A ≥ 6 tested. d_n^{A−1}P_0 is integral in all 10 triples |
| 3 | Trace forms at q = ±φ⁻², 2−√3, −(3−2√2), built exactly in ℚ(√d): Laurent integrality of Δ_nP; (9.1) exactly; balancing (9.3); \|Δ′\| ≤ M_n/2; ℓ ∈ ℤ; Lemma 4.1; L_n = (Δ′ − q^{−e}σΔ′)S_n | `f_forms.py` / `f_forms.log` | 28 cases (7 triples × 4 units): **all pass**. Relative errors 10^{−456} to 10^{−499} at 500 digits |
| 4 | Explicit bound of Lemma 9.2 against c_{s,j}(q) | `f_coef.py` / `f_coef.log` | 5 triples × 7 values of q (units of both signs, ±0.9, 0.3+0.5i): holds everywhere, max ratio 0.021 |
| 5 | τ(4,1), τ(12,2), best r for A ≤ 12; 1 − α/β = 1 + τ; α ≥ 0 ⇔ τ ≤ 0; limit and optimum t* = 0.74429, constant 0.671784; ⌈t*√A⌉ admissible for even A in [6, 2·10⁵]; unbalanced bound and 0.5398; KRZ (3.4) = (dec+coef)/(deg+2coef) and 1 + τ = 2δ (symbolic); δ(12,2) = 1.080059; 12/π² − 2 | `f_num.py` / `f_num.log` | All confirmed. A = 10 gives only 1.939, so A = 12 is the first A with 1 + τ > 2 |
| 6 | Lemma 7.1: 𝒯(n) ≤ Σ_odd + Σ_half ≤ (3n²+6n+2)/8 ≤ 3(n+1)²/8 | `f_num.log` | True for n ≤ 20000 |
| 7 | Remarks 8.1 and 8.2 numerics | `f_t1.py` / `f_t1.log` | Points 4 and 5 |
| 8 | Lean axioms | `axioms_rerun.txt` | `[propext, Classical.choice, Quot.sound]` for all six theorems |
| 9 | Lean build current, no `sorry` | `lake_build.txt` | "Build completed successfully (9073 jobs)", modules replayed, only linter warnings, no `sorry` |
| 10 | Lean names, statements and definitions; chronology | grep / `git log`, `git diff` | Point 2. All 31 names in §11 resolve. Statements and definitions are verbatim. `Defs.lean` and `Statements.lean` are touched only by `97a29ad`. No `sorry`, `axiom`, `native_decide` or `implemented_by`. `Cost/Cyclo.lean` is the only adapted file, matching its header and `NOTICE` |
| 11 | Build | `build/` (scratch) | No undefined references or citations, no overfull boxes, no bibtex warnings |

### Manual verifications, beyond the scripts

- **Lemma 9.2.** I checked by hand:
  - the radius ρ = (1−κ)/2 and the separation of the poles (\|u_i\| ≥ 1−κ);
  - 1−ρ−κ = ρ and (1+ρ)κ < 1;
  - each of the five factor bounds, with the exponent sums rnj + rn(rn+1)/2 and −j(j+1)/2;
  - rnj + je = Anj/2, hence 𝓔(j) and max 𝓔 ≤ (A+4r²)n²/8 + rn/2;
  - the C_s coefficient sum s and the W bounds.
- **Balancing and Lemma 9.3.**
  - Uniqueness of m. M_n/\|Δ′\| = κ^{2m}ϱ_n ≥ 2. M_n² = κ^{2m}ϱ_n·κ^{−e}\|Δσ Δ\|.
  - log M_n = ½ log\|NΔ\| + O(n).
  - The traces for d ≡ 1 and d ≡ 2, 3 (mod 4).
  - (b) term by term, using σ√d = −√d.
  - (c) and (d) with the bound (\|Δ′\| + M_n)\|P\|.
- **Nesterenko.**
  - The n² statement is KRZ's Prop. 2 verbatim (local copy of KRZ).
  - FZ Theorem A requires 0 < α < 1 < β, which here is α < 0 < β; the case α ≥ 0 is handled in the proof.
  - The reindexing n = ⌊√N′⌋ is correct. Repeated forms are allowed.
- **Comparisons against the local texts.**
  - KRZ §3.1 B–D (the constants) and (3.4).
  - KRZ's remark at the end of §3.5 (Jadot, the conjectured limit).
  - FZ Theorems 4 and 6.
  - KRZ §5: the denominator conjecture for S̃_n, proved by JM.
- **Remark 8.3 (ζ_F).** Splitting by the parity of m gives:
  - for even m, (N²−1)/8-weighted Lambert series over odd N at q = φ⁻², that is ζ_q(l) − 2^{l−1}ζ_{q²}(l) with l = 1, 3;
  - for odd m, χ₋₄-twisted odd-weight Eisenstein values at φ⁻¹.

  The remark is correct.
- **Introduction.**
  - The equivalence with s = q + q^{−1} ∈ ℤ, \|s\| ≥ 3.
  - The admissibility and units of ℤ[η].
  - The example 2−√3 ∉ ±η^{−2}.
  - The proof of Corollary 1.4: U_{m+1} − ηU_m = η̄^m and q = Qη^{−2}.
  - The concurrent-work implications.
