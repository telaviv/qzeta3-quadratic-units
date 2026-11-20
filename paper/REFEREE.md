# Referee report

**Paper:** "Irrationality of √d·ζ_q(3) at real quadratic units" (`paper/main.tex`, compiled `paper/build/main.pdf`,
15 pp.). **Date:** 2026-11-19.

**Scope.** Sections "Many values" and "Related work", the repository-URL TODOs and the T2 bullet are placeholders and
were not reviewed (see point 20 for the one dependency).

## Recommendation

**Minor revision.**

## Summary

The paper proves that √d·ζ_q(3) ∉ ℚ when q is a real quadratic unit of norm +1 with 0 < |q| < 1. As corollaries it
gets Σ m²(U_{m+1}/U_m − η) ∉ ℚ for quadratic-unit Lucas sequences, which covers Fibonacci and Pell. The method:
- the A = 4, r = 1 rational function of Krattenthaler–Rivoal–Zudilin, summed bilaterally;
- the reciprocity P_3(1/q) = q^{−n}P_3, P_0(1/q) = −q^{−n}P_0;
- a norm argument at the unit, with denominators d_n⁴ and the elementary bound Σ_{ℓ≤n}φ(ℓ) ≤ 3(n+1)²/8.

I checked every lemma of §§2–7 line by line: every power of q and T, every sign, every summation range, the
even/odd bookkeeping, the W-identity, and the final exponent 4·(3/8) − 2 = −1/2. I also tested the identities by
exact computation in ℚ(q) and numerically (list at the end). The Lean section was compared with the repository and
its git history.

**I found no mathematical error in the proof of Theorem 1.1 or of Corollaries 1.2–1.3.** Every load-bearing lemma
holds as stated, for general (A, r) where claimed. The exact checks in ℚ(q) pass for 9 parameter triples, and
negative controls fail as they should.

The errors are elsewhere:
1. The abstract calls the Lucas corollary *equivalent* to the theorem. It is strictly weaker (point 1).
2. The construction is attributed to KRZ more literally than it should be. KRZ's summand carries an extra factor
   q^k. So the paper's S_n is **not** KRZ's S_n^{[1]} "up to normalisation", as the remark after Lemma 4.1 says
   (point 2).
3. The numerical remark in §7 states a range that holds only at sampled n, and for a modified δ_n (point 3).
4. The "irrationality measure by the usual argument" needs a coefficient bound the paper does not have (point 4).

The Lean section is accurate in substance:
- the quoted statements and definitions are verbatim;
- the forms of the ingredients are described correctly;
- the axiom output, the absence of `sorry`, the versions, the line count and the provenance all check out.

The frozen-statement chronology is stated a little too strongly (point 13).

## Numbered points

### Mathematics and factual accuracy

1. **(major: false statement, one-word fix) Abstract, lines 50–51: "Equivalently, for every unit η > 1 …".**
   - Corollary 1.2 is Theorem 1.1 at q = η̄/η = Q/η², that is, only at q ∈ ±(O_K^×)².
   - Theorem 1.1 covers every norm-+1 unit. Take K = ℚ(√3) and q = 2 − √3 = (2+√3)^{−1}. The units of every order
     in K are ±(2+√3)^k, so Q/η² = ±(2+√3)^{−2k}, and q is not of that form. Hence √3·ζ_{2−√3}(3) ∉ ℚ follows from
     the theorem but not from the corollary.
   - The body says this correctly (lines 127–128). Only the abstract overstates.
   - *Fix:* "In particular" instead of "Equivalently". Optionally add one sentence after Corollary 1.2: it covers
     exactly q ∈ ±(O_K^×)².

2. **(minor: wrong attribution in remarks that the proof does not use) Lines 154, 174–175, 189–190, 359–364, 431.**
   - Line 190 says R "is the summand of [KRZ06, §3] without its factor q^{−(A−2r)n/4}". That is false.
     - KRZ's series (p. 5) is S_n(q) = (q;q)_n^{A−2r} Σ_k **q^k** (q^{k−rn};q)_{rn}(q^{k+n+1};q)_{rn}/(q^k;q)_{n+1}^A ·
       q^{(k−1/2)(A−2r)n/2}.
     - Equivalently (KRZ §3.3), S_n(z;q) = Σ_k q^k R_n(q^k;q) z^{−k}.
     - The paper's R is KRZ's rational function R_n(T;q) of §3.3 without q^{−e/2}. But the paper sums R(q^k), not
       q^k R(q^k): the weight is T^e, not T^{e+1}.
   - The remark after Lemma 4.1 (lines 359–364) says "Up to normalisation, this is the combination S_n^{[1]}". That
     is false.
     - A direct computation from KRZ's definitions, using their Lemma 2 (R_n(q^nT;1/q) = R_n(T;q)), gives
       S_n^{[1]} = q^{−e/2}[Σ_k (T·R(T))_{T=q^k} − Σ_k (T·R(T))_{T=q^{−n−k}}]. This is the paper's construction with
       T^{e+1} in place of T^e.
     - [Numerical, N5] At q = φ^{−2}, S_n^{paper}/S_n^{[1]} has log|·|/log(1/q) = 2.13, 3.02, 4.00, 5.00 for
       n = 2, 4, 6, 8. That is ≈ n/2 + 1, a ratio that depends on n, so it is not a normalisation.
     - For the same reason, KRZ's §4 remark (q-analogue of Beukers–Gutnik–Nesterenko) is about their series, not
       "this series".
   - Line 431 ("the same limit"): KRZ Lemma 4 is about their series. The n² limit agrees, but the series is not the
     same. Remark 7.4 cites KRZ Lemma 5 for the size of P_0, which also concerns their coefficients; as a statement
     about the present P_0 it is heuristic.
   - None of this affects the proofs: §§2–7 are self-contained, and every identity was checked for the paper's own R.
     Lemma 2.2 does match KRZ's Lemma 2 after renormalisation. The same misattribution is in PROOF_T1 §§1 and 3, and
     REFEREE_T1 missed it.
   - *Fix:*
     - Line 190: "This is the rational function R_n(T;q) of [KRZ06, §3.3] without its factor q^{−(A−2r)n/4}. KRZ sum
       q^kR_n(q^k); we sum R_n(q^k)."
     - Line 154: "a variant of the series of [KRZ06, §3] (weight T^e instead of T^{e+1}), summed bilaterally".
     - Lines 359–364: delete the remark, or state the correct relation above.
     - Line 431: "KRZ obtain the analogous limit for their series".

3. **(minor: factual error in a remark the proof does not use) Remark after the proof of Theorem 1.1, lines 509–513.**
   - The claim: the bracket "computed with 6δ_n … lies in [−0.80, −0.71] for 6 ≤ n ≤ 30, at both q = φ^{−2} and
     q = −φ^{−2}".
   - I recomputed it for **every** n in 6..30 [Numerical, N3]. S_n was summed directly (no cancellation) and
     N(d_n) computed as an exact integer.

     | δ | q = φ^{−2} | q = −φ^{−2} |
     |---|---|---|
     | d_n⁴ (the paper's δ_n) | [−0.819, −0.582] | [−0.840, −0.719] |
     | 6d_n⁴ | [−0.792, −0.506] | [−0.801, −0.657] |

   - The stated range is reproduced only at n ∈ {6, 10, 14, …, 30}, the sample of `bracket_A4.py`. Rerunning that
     script gives −0.7155, −0.7578, …, −0.7828 at φ^{−2}, matching my 6d_n⁴ values at those n. At n = 7, for
     example, 6d_n⁴ gives −0.506 at φ^{−2}.
   - The factor 6 (inherited from the general-A denominator (A−1)!) is unexplained in the paper. It is not small at
     n = 6: log 36/(36·log φ²) ≈ 0.10.
   - The value is printed as "12/π² − 2 = −0.7842…". The correct value is −0.78414…, so write −0.7841….
   - *Fix:* drop 6δ_n and state the d_n⁴ figures for all 6 ≤ n ≤ 30 (the table above). For example: "oscillates
     around 12/π² − 2, between −0.84 and −0.58".

4. **(minor: unsupported claim) Same remark, lines 513–514: "The margin gives an irrationality measure … by the usual
   argument".**
   - For an approximation a/b ≠ α = θζ_q(3), put y_n = bDδ_nP_0 + aθδ_nP_3. Then
     - y_n = bDδ_nS_n + θδ_nP_3(a − bα);
     - σ(y_n) = −q^{−n}σ(δ_n)[bDS_n + θP_3(a − bα)].
   - Both places therefore need an **upper bound for |P_3(q)|**, the coefficient bound the paper stresses it avoids
     (line 168). It holds heuristically by KRZ Lemma 5, which is for their series (point 2), but it is not proved
     here.
   - *Fix:* delete the sentence, or say that a measure would also need an upper bound for |P_3|, not proved here.

5. **(minor: compressed step) §4, lines 300–305 (evaluation at a number q), used in §7 line 492.**
   - Lemma 5.1 is an identity between f(1/q) and f(q) in ℚ(q). Evaluating it at q₀ needs two more facts:
     - (i) R_n := ℚ[q, q^{−1}, d_n(q)^{−1}] is stable under q ↦ 1/q. This holds because
       Φ_ℓ(1/q) = q^{−φ(ℓ)}Φ_ℓ(q) for ℓ ≥ 2 and Φ_1(1/q) = −q^{−1}Φ_1(q).
     - (ii) The value of f(1/q) at q₀ equals the value of f at 1/q₀ (and |1/q₀| ≠ 1).
   - Both are trivial, but §7 uses exactly this step ("evaluated at q as explained in Section 4"), and §4 does not
     say it.
   - *Fix:* add one sentence to §4.

6. **(minor: overclaim) Contributions list, line 148: "the explicit Lucas-sequence form of Corollary 1.2".**
   - It is a three-line consequence of Theorem 1.1. It follows equally from [Twi26] at b = 1/q = Qη², which is a
     Pisot unit.
   - The project's own novelty note (`handoff/fibzeta/many/NOVELTY_2.md`, "Consequences") advises: "Do not claim
     priority for T1, or for the Fibonacci series form."
   - *Fix:* drop the bullet, or rephrase it as "we also record the Lucas-sequence form, which follows equally from
     [Twi26]".

7. **(minor) Concurrent work, lines 138–140 ([Twi26b] "for the same b").**
   - Per the source note, [Twi26b] claims independence over ℚ(b) for **Pisot or Salem** b (and over ℚ for integer
     b ≥ 2).
   - [Twi26]'s class is wider: it includes non-real b such as 1 + i.
   - The conclusion ("contains Theorem 1.1") is still right, because 1/q is Pisot.
   - I checked the linear relation: Σ n²/(bⁿ−1) = M_1 + 3M_2 + 2M_3, since k² = 2C(k−1,2) + 3(k−1) + 1. Consider
     stating it.
   - *Fix:* "for Pisot and Salem b".
   - The rest of the paragraph matches `HEXAGON_TWINHETERODOX_2611.md` and `NOVELTY_2.md`: the dates, the
     hypothesis of [Twi26], that ζ_q(3) ∉ K is stronger, and that it builds on the [UPL] Hankel construction.

8. **(minor) Introduction, literature, lines 72–74 and 82–84.**
   - (a) "Let q = 1/p with p ∈ ℤ∖{0, ±1}. For integers p ≥ 2, ζ_q(1) is irrational": the hypotheses do not match.
     Either state Borwein's result for |p| ≥ 2 (if that is what [Bor92] gives), or restrict the setup sentence.
   - (b) "the known results are for weight one: … (Tachiya, Bundschuh–Väänänen)" reads as exhaustive. It omits
     Dixit–Kumar–Pathak 2024 (ζ_q(1) ∉ ℚ(q) for ±q Pisot) and Bundschuh 2007. Both are in `refs.bib` but not cited.
     The Related-work section is a placeholder, so cite them here or write "for example".
   - The other literature statements agree with NOVELTY_2.md and with the KRZ text:
     - KRZ §3.5, the conditional extension via Jadot (checked in the local KRZ copy);
     - BZ07 §6;
     - [PVA07], [JM10], [FZ10];
     - the uplift draft;
     - Nesterenko for the even weights.

9. **(minor) Remark 7.5 (ζ_F(3)), lines 548–553.**
   - "odd parts of ζ_q(3) and ζ_q(1)" is undefined in this paper.
   - [Kri26a, §1] places the modular-form values at q = φ^{−1} and φ^{−2}. The paper only says "at q = φ^{−2}".
   - The last sentence generalises to "ζ_F(s) for odd s", but only s = 3 is discussed.
   - *Fix:* define "odd part" (or say "the part of ζ_q(3) at odd N"), add φ^{−1}, and restrict the conclusion to
     ζ_F(3).

10. **(minor) Remark 7.4 (plain statement), line 541.** "Numerically |P_0| is about |q|^{−n²}" is consistent with my
    run [N4]: log|P_0|/(n² log(1/|q|)) is 0.91–0.95 at n = 12, for six values of q. Label it [Numerical]. Note,
    per point 2, that KRZ Lemma 5 is stated for their coefficients.

### Lean section (§10 in the compiled paper)

11. **Verified as correct.**
    - **Statements and definitions.** The four theorems quoted at lines 590–606 are verbatim from
      `QZeta3/Final.lean`. The three definitions at lines 610–619 are verbatim from `QZeta3/Defs.lean`.
    - **The ingredients.** The descriptions at lines 672–677 match `Statements.lean`:
      - `SizeBound`: S_n ≠ 0 and |S_n| ≤ C|q|^{n(n+1)};
      - `CostBound`: |d_n(q)d_n(q⁻¹)|⁸ ≤ Cⁿ|q|^{−3(n+1)²};
      - `Integrality`: `LaurentInt` for d_n⁴P_0 and d_n⁴P_3, uniform over real x ≠ 0 with |x| ≠ 1;
      - `Recip`: at every real q ≠ 0 with |q| ≠ 1;
      - `Expansion` and `Recip` take `PFIdentity` as a hypothesis.
    - **Names.** `norm_int`, `Gser`, `cc`, `lucasU_one_one`, `epsU_one_one`, `summable_zetaq3` and `summable_lucas`
      exist (the summability lemmas are in `Reduction.lean`).
    - **Trust base and versions.**
      - `scripts/axioms.txt` lists only propext, Classical.choice and Quot.sound.
      - grep finds no `sorry`, `axiom`, `native_decide` or `implemented_by`.
      - Lean and Mathlib are v4.35.0 (`lean-toolchain`, `lake-manifest.json`).
      - `QZeta3/` has 3179 lines ("about 3200").
    - **Provenance.** `NOTICE` and the header of `Cost/Cyclo.lean` say what lines 699–701 say. Cyclo.lean is the
      only adapted file.
    - **Defs vs paper.** `Defs.lean` matches the paper's objects: `Gser` = u⁴R at the pole, `cc` = [u^{4−s}],
      `Wf` = W_{s,j}, `Sn` = the bilateral sum.
    - **Main.lean.** `irrational_sub_inv_mul_zetaq3_of` implements §7 faithfully: Y = bD·X^{c₃}L_0 + a(2X−s)X^{c₀}L_3,
      with 2q⁻¹ − s = −θ.

12. **(minor) "The four theorem statements above were written next, with placeholder proofs" (lines 625–626).**
    - `Defs.lean` and `Statements.lean` are unchanged since the first commit 97a29ad: `git diff 97a29ad HEAD` is empty
      for both. That part of the claim is correct.
    - `Final.lean` was first committed in 9a98dbc (2026-11-18 23:47) with `sorry` proofs. That is **after** three
      ingredients (recip, pf, size: 46b474a, d103e41, a433cf4, 23:44–23:45) were proved and merged.
    - Since 9a98dbc the statement text is unchanged. A whitespace-insensitive diff shows only `:= by sorry` replaced
      by term proofs; the file was also converted to CRLF line endings.
    - The fifth statement then in the file, `summable_zetaq3`, moved to `Reduction.lean`.
    - "Written next" thus suggests a stricter order than git shows. It is harmless, since the final statements do not
      mention the ingredients.
    - *Fix:* "were committed (9a98dbc) with placeholder proofs before the last three ingredients were proved, and
      their text is unchanged since".
    - Also, the blind back-translation (`FIDELITY.md`) compared the statements with PROOF_T1's statement, not with
      Theorem 1.1 of this paper. It is the same content, but say so.

13. **(minor) Commit, line 585.** The paper cites 6318359. HEAD is ca3ef6a, which changes only `CLAUDE.md` and
    `STATEMENT_REVIEW.md` (no Lean file). Cite the commit that will be published, or say that the Lean sources are
    identical.

14. **(minor) Table, lines 657–671.**
    - The Corollary row names `lucas_sum_eq`, which is only the series identity. The irrationality assembly is
      `irrational_lucas_sum_ing` (`Reduction.lean`); the algebra is `term_eq`, `qU_add_inv` and `discr_mul_sq`
      (`Corollary.lean`).
    - The √d form (`irrational_sqrt_mul_zetaq3_ing`) has no row.
    - *Fix:* add both.

### Exposition and notation

15. **(exposition) Symbol clashes.**
    - **Φ** is both the ℓ-th cyclotomic polynomial Φ_ℓ (§3, §6) and the summatory totient Φ(n) (§6). Both appear in
      the proof of Lemma 6.1. Rename Φ(n), e.g. to Σ_φ(n) or 𝔉(n).
    - **D** is P² − 4Q (lines 105, 518) and θ² (line 485). Use Δ for the discriminant.
    - **s** is the trace q + q⁻¹ (line 99, Lean section) and the pole order s (from §3 on).
    - **E** is Σ −log(1 − κ^a) (Lemma 6.1) and the Lean Lucas parameter E (§10).
    - **P** is the Lucas parameter, the coefficients P_0, P_3, P_l, and the Pell numbers 𝒫_m (𝒫_3 next to P_3).
    - **a, b** are a divisor (Lemma 6.1), b = h − j′ (Lemma 3.2), and the fraction a/b (§7).
    - **c** is c_{s,j}, c_±, and c = 1 − b − n (Lemma 3.2).
    - **C** is a constant (Lemma 5.1) and C_s(x).
    - In Lemma 3.2, i indexes the factors f_i and i′ the linear factors, in the same formula.
    - φ_E for Euler's function is non-standard. It is needed only because φ is the golden ratio; say so, or use
      ϕ / φ consistently.

16. **(exposition) Line 160–161: "whenever σ acts on the value by −1, that is, whenever ζ_q(3) ∈ ℚ√d".** σ is defined
    only on K. *Fix:* "if ζ_q(3) ∈ ℚ√d, then S_n ∈ K and σ(S_n) = −q^{−n}S_n".

17. **(exposition) Abstract, lines 54–55: "this makes the linear forms small at both archimedean places".** True only
    under the hypothesis √dζ_q(3) ∈ ℚ. Add "if √d ζ_q(3) were rational".

18. **(exposition) Lemma 5.1, line 405.** Note that C depends on q and A. Also, the second display uses
    |1 − q^{A(n/2+k)}| ≤ 2 for all k ≥ rn + 1, which needs the same "n large" as the lower bound (it is stated, but
    only once).

19. **(exposition) Lemma 3.2.** The final step is clear. It would help to say explicitly that the constant term a_{i,j}
    (M_i = 0) needs no denominator, and that T^e contributes no denominator either.

20. **(exposition) Dependence on the placeholders and the build.**
    - Sections 2–5 are written for general even A and 1 ≤ r < A/2 (line 173) only to serve the "Many values"
      section. If that section is deleted, consider specialising to A = 4, r = 1. That would also match the Lean
      statements.
    - The commented-out TODO in §8 quotes the constant 0.540. `PROOF_T2.md` now claims 0.672. This is a comment
      only.
    - `build/main.pdf` (15:35) is older than `main.tex` (15:53). Rebuild before circulating.

## Computer checks run

All scripts are in `paper/referee_scratch/`. They are independent of the authors' scripts, except where stated.

**Exact, in the field ℚ(q) (and ℚ(q)(T)), `sym_fast.py`, log `sym_fast.log`.** Run for (A, r, n) = (4,1,1), (4,1,2),
(4,1,3), (4,1,4), (4,1,5), (6,1,2), (6,2,2), (6,2,3), (8,3,2). **All OK:**

| Check | Paper result | Identity checked |
|---|---|---|
| C1 | Lemma 2.1 | R(q^{−n}/T) = q^{An/2}T^A R(T) |
| C2 | Lemma 2.2 | R(T;1/q) = q^{−e}R(q^{−n}T;q) |
| C3 | (3.1) | partial fractions, with c_{s,j} := [u^{A−s}] u^A R at T = q^{−j}(1−u) (the Lean definition) |
| C4 | §3 | Σ c_{s,j} = 0 |
| C5 | Cor. 3.1 | c_{s,j}(1/q) = q^{−e}c_{s,n−j}(q) |
| C6 | Lemma 3.2 | d_n^{A−s}c_{s,j} ∈ ℤ[q^{±1}] |
| C7 | §5 | W_{s,n−j}(1/q) = −W_{s,j}(q) − n |
| C8 | Lemma 5.1 | P_l(1/q) = q^{−e}P_l (odd l ≥ 3), P_0(1/q) = −q^{−e}P_0; Q_0 = 0 |
| C9 (A = 4) | §7 | P_3 = Σ_j (c_{3,j} + 2c_{4,j}); d_nP_3 and d_n⁴P_0 ∈ ℤ[q^{±1}] |

- [info] d_n³P_0 is also integral for n ≤ 5. This extends REFEREE_T1's n ≤ 6 remark at A = 4.
- Negative controls (n = 3) fail, as they should:
  - d_n·c_{1,j} is not integral;
  - d_n²·c_{1,j} is not integral, so the exponent A − s in Lemma 3.2 is sharp here;
  - c_{s,j}(1/q) = q^{+e}c_{s,n−j} is false.
- `sym_checks.py` (a slower sympy-series version of the same checks) was abandoned for speed. It produced no result.

**Numerical, mpmath, `num_checks.py`, logs `N1.log`, `N3.log`.**
- **N1, Lemma 4.1.**
  - The direct bilateral S_n equals P_0 + P_3ζ_q(3), with relative error ≤ 10^{−273}.
  - Parameters: n ∈ {1, 2, 3, 5, 8, 12}; units q = φ^{−2}, −φ^{−2}, 2 − √3, −(3 − 2√2); non-units q = 0.37, −0.6.
  - 500 digits; P_0 and P_3 come from my own truncated-series partial fractions.
- **N2, Lemma 5.1.** log|S_n| + n(n+1)log(1/|q|) stabilises (to −2.19, 0.61, −1.24, 0.40, −2.07, 0.37) for these q.
- **N3, bracket of the §7 remark.**
  - Computed for every 6 ≤ n ≤ 30 at q = ±φ^{−2}: N(d_n) as an exact integer (Möbius product, rounded, with a
    10^{−50} check), S_n summed directly.
  - The results are the table in point 3. Rerunning the authors' `bracket_A4.py` (log `bracket_A4_rerun.log`)
    reproduces my 6d_n⁴ values at its sampled n.
- **N4.** log|P_0|/(n² log(1/|q|)) = 0.91–0.95 at n = 12 (point 10).
- **N5, comparison with KRZ.** KRZ's S_n^{[1]} was computed from their definition: summand with q^k, normalisation
  q^{−e/2}, S_n(1/q) summed directly. It agrees with q^{−e/2}·(the bilateral sum with T^{e+1}) to all digits. The
  ratio to the paper's S_n is ≈ q^{−(n/2+1)} (point 2).

**Miscellaneous, `misc_checks.py`.**
- **M1.**
  - Φ(n) ≤ (3n² + 6n + 2)/8 ≤ 3(n+1)²/8 for all n ≤ 200000, and the intermediate bound (sum of odd ℓ plus Σ_{m≤n/2} m)
    holds.
  - max Φ(n)/(n+1)² = 0.304.
  - φ(2m) ≤ m for all m ≤ 10⁵.
- **M2.** Σ m²(U_{m+1}/U_m − η) = √D·ζ_{Q/η²}(3) to 10^{−55}, for (P,Q) = (1,−1), (2,−1), (3,−1), (5,−1), (3,1),
  (4,1), (7,1). The second Fibonacci form Σ(−1)^m m²/(φ^m F_m) agrees to 10^{−55}.
- **M3.** q = 2 − √3 is a norm-+1 unit not of the form ±η^{−2} (point 1).
- **M4.** The exponent 4·(3/8)(n+1)² − 2n(n+1) + n = −n²/2 + 2n + 3/2.

**Repository checks.**
- `git log`, `git diff 97a29ad HEAD`, and the whitespace-insensitive `git diff 9a98dbc 6318359 -- QZeta3/Final.lean`
  (point 12).
- grep for `sorry`, `axiom`, `native_decide`, `implemented_by`, `extern` and `unsafe`: none.
- `wc -l`: 3179 lines in `QZeta3/`.
- `lean-toolchain` and `lake-manifest.json`: v4.35.0.
- `NOTICE` and the Cyclo.lean header.
- A rerun of `lake env lean Axioms.lean` was started; see the addendum below.

**By hand (beyond the scripts).**
- **Lemma 2.1:** all four factor transformations, the T-power A(n+1) − 2rn − 2e = A, the q-power An/2, the sign.
- **Lemma 2.2:** the q-power rn, then rn − An/2 = −e.
- **Lemma 3.2:**
  - the block decomposition (A factors);
  - the Vandermonde-type product ±q^{−j′(j′+1)/2}(q;q)_{j′}(q;q)_{n−j′};
  - b ≤ −n for type 2 and b ≥ 1 for type 3;
  - the u-coefficient (−q^{j′−j})^{M−1}α^{−M};
  - the degree distribution.
- **Lemma 4.1:**
  - the ranges m ≥ j+1 and m ≥ n−j+1;
  - (−1)^s C(i−1, s−1) = −C_s(−i), with both sides vanishing for 1 ≤ i < s;
  - Q_0 = Σc = 0, λ ≤ A − 2;
  - absolute convergence.
- **Lemma 5.1:** the W-identity and the cancellation of the −n term.
- **Lemma 5.2 (size):** R(q^k) = 0 for k ≤ rn, the count A − 2r + 2 ≤ A, the tail ratio 4C²κ^e/(1−κ^e).
- **Lemma 6.1:** the Möbius product, Σ_{a|ℓ} aμ(ℓ/a) = φ(ℓ), |log|1−q^a|| ≤ −log(1−κ^a), and the odd/even split
  ⌈n/2⌉² + ⌊n/2⌋(⌊n/2⌋+1)/2 ≤ (3n² + 6n + 2)/8.
- **§7:**
  - [x²]C_3 = 1/2 and [x²]C_4 = 1;
  - y_n ∈ O_K;
  - σ(f(q)) = f(1/q) for f ∈ ℤ[q^{±1}];
  - σ(y_n) = −q^{−n}d_n(1/q)⁴bDS_n;
  - |N y_n| = b²D²κ^{−n}|N d_n|⁴|S_n|².
- **Remark 6.2:** with Φ ≤ n(n+1)/2 the bracket is +n·log(1/κ) + O(n), so "would not suffice" is right.
- **Corollaries:** Binet, U_{m+1} − ηU_m = η̄^m, q = Q/η², σq = 1/q, D not a square for admissible (P, Q).

**Addendum (axiom rerun).** The rerun of `lake env lean Axioms.lean` hit my 15-minute timeout (exit 124) without
printing anything. This looks like the cold `import Mathlib` that the repo's CLAUDE.md warns about, not an error. So I
did **not** independently reproduce `scripts/axioms.txt`. The axiom claim rests on that file (its mtime is after the
last Lean edit) and on the grep above. A warm rerun before posting is advisable.
