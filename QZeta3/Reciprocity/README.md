# QZeta3/Reciprocity — `recip (hpf : PFIdentity) : Recip`

Source: `handoff/fibzeta/many/PROOF_T1.md`, Lemma 2, its Corollary, and Lemma 5 (A = 4, r = 1, k = n).

| Lean | PROOF_T1 |
|---|---|
| `Coeff.lean: qPoch_inv_sq` | (1/q;1/q)_n = ±q^{−n(n+1)/2}(q;q)_n, in squared form |
| `Coeff.lean: qPoch_inv_shift1/2` | the two numerator blocks trade places under q ↦ 1/q (proof of Lemma 2) |
| `Coeff.lean: eval_Npoly_inv`, `Npoly_comp_inv` | Lemma 2 for the numerator: N(q^n V; 1/q) = q^{−n} N(V; q) |
| `Coeff.lean: Dother_inv` | other-pole product invariant under (q, j) ↦ (1/q, n − j) |
| `Coeff.lean: Gser_inv`, `cc_inv` | Corollary of Lemma 2: c_{s,j}(1/q) = q^{−n} c_{s,n−j}(q) |
| `Top.lean: Wf_inv` | W_{s,n−j}(1/q) = −W_{s,j}(q) − n (proof of Lemma 5) |
| `Top.lean: sum_cc_eq_zero` | Σ c_{s,j} = R(0) = 0 (from `PFIdentity` at T = 0) |
| `Top.lean: recip` | Lemma 5: P3(1/q) = q^{−n}P3(q), P0(1/q) = −q^{−n}P0(q) |

Numerical check of the intermediate identities (exact, q = 2/7): `scripts/recip/check_recip_lemmas.py`.
