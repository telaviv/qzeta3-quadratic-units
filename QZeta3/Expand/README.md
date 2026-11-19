# QZeta3/Expand — Lemma 4 (expansion), A = 4

`theorem QZeta3.Expand.expansion (hpf : PFIdentity) : Expansion` in `Top.lean`.

| Lean | PROOF_T1 §3 |
|---|---|
| `sum_cc_zero` | Σ_{s,j} c_{s,j} = R_n(0) = 0 (PFIdentity at T = 0) |
| `Rfun_pos` | positive side: R(q^{k+1}) = Σ c_{s,j}[(1 − q^{j+k+1})^{−s} − 1] |
| `Rfun_neg` | negative side: R(q^{−n−k−1}) = Σ c_{s,j}(1 − q^{j−n−k−1})^{−s} |
| `hasSum_pos`, `hasSum_neg` | sum over k: F_s − Σ_{m≤j}, G_s − Σ_{m≤n−j} (shifted series) |
| `fS_sub_gS` (Analytic) | termwise (1−y)^{−s} − 1 − (1−1/y)^{−s} = 2y/(1−y) + aS(s)·y(1+y)/(1−y)³, aS = 0,0,1,2 |
| `hasSum_sq_geom` (Analytic) | Σ_{i≥1} i² rⁱ = r(1+r)/(1−r)³ |
| `hasSum_zet` (Analytic) | Σ_m q^m(1+q^m)/(1−q^m)³ = ζ_q(3) (swap of an absolutely convergent double series) |
| `summable_lam`, `summable_gS`, `summable_fS` | absolute convergence of every split series |
| `Fsum_sub_Gsum` | F_s − G_s = 2L + aS(s)·ζ_q(3) |
| `expansion` | assembly: S_n = Σ c(F − G) + P₀ = 2L·Σc + P₃ζ_q(3) + P₀ |
