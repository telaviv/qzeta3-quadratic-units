# Response to the first referee (REFEREE.md, T1 parts; minor revision), 2026-11-19

That referee read the paper before T2 and the related-work section were merged (both were placeholders then). The final
whole-paper referee, covering T2 and the Lean section, is `REFEREE_FINAL.md`, with its response at the end of this file.

| # | point | action |
|---|---|---|
| 1 | Abstract: "Equivalently" is false | The abstract is rewritten around T2 and now says "In particular". After the corollaries, a new sentence says that Corollary 1.4 covers only q = ±η⁻², with q = 2 − √3 as an example of a unit it misses. |
| 2 | Wrong attribution to KRZ | Changes: §2 now says "R_n(T;q) of [KRZ, §3.3] … KRZ sum q^kR_n(q^k); we sum R_n(q^k)"; the method paragraph says "a variant … (weight T^e instead of T^{e+1}, summed bilaterally)"; the remark after Lemma 4.1 now says S_n^{[1]} is built from TR(T) and is not a multiple of our S_n (the BGN sentence is dropped); after Lemma 5.1 it reads "the analogous limit for their series"; the plain-statement remark now cites our own Lemma 8.2 for the upper bound on P_0, and KRZ §3.5 only for their series; the T2 coefficient lemma is "the analogue for our coefficients of [KRZ, Lemma 5]". |
| 3 | Numerical remark range and 6δ_n | Rewritten with d_n⁴ and the referee's recomputed ranges for all 6 ≤ n ≤ 30: [−0.82, −0.58] at φ⁻² and [−0.84, −0.72] at −φ⁻². The value is now 12/π² − 2 = −0.7841…. |
| 4 | Irrationality measure | Now says a measure would also need an upper bound for \|P_3(q)\| (available from Lemma 8.2), and that we do not pursue it. |
| 5 | Evaluating f(1/q) | §4 now states that ℚ[q^{±1}, d_n^{−1}] is stable under q ↦ 1/q (because Φ_ℓ is self-reciprocal) and that values at q of f(1/q) are values of f at 1/q. |
| 6 | Lucas form overclaimed | The bullet now reads "the Lucas-sequence form of these results; for Theorem 1.3 it follows equally from [Twi26]". |
| 7 | [Twi26b] class | Now uses the class from its abstract (algebraic integers with all other conjugates, apart from b̄, in the closed unit disk). The relation ζ_{1/b}(3) = M₁ + 3M₂ + 2M₃ is stated, with its proof. |
| 8 | Literature hypotheses and exhaustiveness | (a) Changed to "For p ≥ 2". (b) The list is now "for example …" and adds DKP24, with a pointer to the new Related-work section (which also cites Bundschuh 2007 and BV05b). |
| 9 | ζ_F remark | Rewritten: the parity split gives ζ_q(l) − 2^{l−1}ζ_{q²}(l), l ∈ {1, 3}, at q = φ⁻², plus odd-weight χ₋₄ Eisenstein values (following handoff/fibzeta/many/RESULT.md §5). The conclusion is restricted to ζ_F(3). |
| 10 | \|P_0\| numerics | Now labelled as numerical, with the referee's range (0.91–0.95 at n = 12, six q). |
| 11 | Lean checks | No action needed. |
| 12 | Chronology of Final.lean; FIDELITY compared with PROOF_T1 | Now reads "committed with placeholder proofs before the last three ingredients were proved; text unchanged since". The FIDELITY sentence now says it compared with the author's working statement (same content). |
| 13 | Commit | The paper now says the Lean sources are those of 6318359 and that later commits change only documentation and the paper. The URL stays a marked TODO for the owner. |
| 14 | Table | Added rows for `irrational_sqrt_mul_zetaq3_ing` and `irrational_lucas_sum_ing`. |
| 15 | Symbol clashes | Renamed: Φ(n) → 𝒯(n); E → B in Lemma 6.1; D → θ² in §7; φ_E is explained ("φ denotes the golden ratio"). Kept: s (trace, used only in the intro and the Lean section), P (Lucas parameter versus P_l, which never meet in one formula), and a, b, c, C (local). |
| 16 | "σ acts on the value" | Now reads "suppose ζ_q(3) ∈ ℚ√d. Then S_n ∈ K and σ(S_n) = −q^{−n}S_n". |
| 17 | Abstract "small at both places" | Now reads "suitable integer linear forms in the twisted values √d ζ_q(l)". |
| 18 | Lemma 5.1 constant | Added that C depends only on κ and A. |
| 19 | Lemma 3.2 final step | Added the sentence on the M_i = 0 terms and T^e. |
| 20 | Placeholders and build | §8 (T2) is merged, so general (A, r) is now used. The stale comment is gone. Rebuilt. |

**Axiom rerun (the referee's open item).** A warm `lake env lean Axioms.lean` (2 min 10 s) printed
`[propext, Classical.choice, Quot.sound]` for all six final theorems. The output is in `referee_scratch/axioms_rerun.txt`.

# Response to the final whole-paper referee (REFEREE_FINAL.md, accept after minor revision), 2026-11-19

| # | point | action |
|---|---|---|
| 1 | Repository URL | Left as `\TODO{public repository URL}` (two places, intro and §11) for the owner, who is naming the repo now. Follow-up commit. |
| 2 | Chronology; "later commits" | Now says "before the last two ingredients were proved". The paper is committed with this change, so "later commits change only documentation and this paper" holds. The docstring slip in `Reduction.lean` is outside `paper/` and left for the owner. |
| 3 | Reason for proving the coefficient lemma | Now says "because our coefficients c_{s,j} are not those of [KRZ06], and because we want an explicit bound". |
| 4 | \|P_0\| range | Now [0.90, 0.95], naming the seven units. |
| 5 | "oscillates around" | Now "stays near". The ranges are unchanged. |
| 6 | [UPL] "proves" | Now "claims … with a Lean formalisation of its main theorem (not checked by us)". |
| 7 | Related-work concurrent paragraph | (a) Only [Twi26] builds on [UPL]. (b) ζ_q replaced by ζ_{1/b}. (c) The class is the one from the introduction, which contains Pisot and Salem. |
| 8 | "same machine" | Intro and Remark 9.4 now say "the same leading constants (decay, coefficient size and denominator, which our variant shares with KRZ) and the same single-form criterion". |
| 9 | Notation | Renamed c_3, c_4 → γ_−, γ_+, and the Lucas-extension weight s → l. Other clashes are local and left as they are. |
| 10 | Choice of d | The balanced trace forms subsection now starts with "d is squarefree; the general case is reduced to it at the end of the proof". "For large n" is dropped. |
| 11 | Abstract "invariant" | Now "invariant or anti-invariant under q ↦ 1/q, up to a power of q". |
