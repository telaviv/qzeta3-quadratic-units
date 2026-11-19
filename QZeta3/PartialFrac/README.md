# PartialFrac: (2.1) of PROOF_T1

`QZeta3.PartialFrac.pfIdentity : PFIdentity` (in `Top.lean`).

| Lean | PROOF_T1 §2 step |
|---|---|
| `Basic.lean`: `Lin`, `Oth`, `Dpoly`, `Qpoly`, `Hpoly` | `1 − q^j T`, `∏_{j'≠j}(1 − q^{j'}T)⁴`, `D(T)`, principal part `Σ_s c_{s,j} u^{4−s}`, `H = N − Σ_{j,s} c_{s,j}(1 − q^jT)^{4−s}∏_{j'≠j}(…)⁴` |
| `natDegree_hpoly_le`, `natDegree_dpoly` | `deg H ≤ 4n+3 < 4(n+1) = deg D` (uses `deg N ≤ 3n`) |
| `ncomp_eq` | `N(q^{−j}(1−u)) = Gser · Dother` in `𝕜⟦u⟧` (constant coefficient of `Dother` is `∏(1 − q^{j'−j})⁴ ≠ 0`) |
| `gser_sub_qpoly_dvd` | `u⁴ ∣ Gser − Σ_s c_{s,j} u^{4−s}`, since `c_{s,j} = [u^{4−s}] Gser` |
| `hcomp_dvd` | `u⁴ ∣ H(q^{−j}(1−u))` (the `j₂ ≠ j` terms contain `(1 − q^jT)⁴ ↦ u⁴`) |
| `lin_pow_dvd_of_comp` | pull back along `u = 1 − q^jT`: `(1 − q^jT)⁴ ∣ H` |
| `lin_pow_coprime`, `hpoly_eq_zero` | pairwise coprime ⇒ `D ∣ H` ⇒ `H = 0` by degree |
| `pf_generic` | evaluate at `T`, divide by `D(T)`; any field, `q ≠ 0`, `q^i = q^k ⇒ i = k` |
| `pfIdentity` | real `q` with `|q| ≠ 1`: `q ↦ q^i` is injective |
