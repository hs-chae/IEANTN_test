# Strict-open prime counts between real cubes

## Results (strict-open, all n real)

| Coefficient of n²/log n | Domain | Inputs beyond ordinary foundations | Verification |
|---|---|---|---|
| **0.7803** | n≥exp(8) | Same inherited octic package: RH + Green + Nicolas + BPT | Written proof, exact scalar checks |
| **0.96699** | n≥369, hence n≥exp(8) | RH + Schoenfeld (6.1) + Büthe (1.6)–(1.7); no Green/Nicolas/BPT | Lean kernel |
| **0.9848** | n≥1737, hence n≥exp(8) | Original RH/Green/Nicolas/BPT general sources **plus** Büthe; no Schoenfeld | Written proof, exact scalar checks; not independently reviewed or Lean-formalized |
| 0.98010 | n≥1013 | Same as 0.9848 (two-notch proof) | Written proof, exact scalar checks |
| 0.98839 | n≥exp(8), (n+1)³≤10¹⁹ | Büthe alone (historical unconditional computation) | Lean kernel |
| 0.74347 | n≥exp(8) | RH + Schoenfeld alone | Lean kernel |
| 0.692 | n≥1321 | RH + Schoenfeld alone | Lean kernel |
| 0.98 / 0.99 / 0.999 | n≥exp(16) / exp(18) / exp(24) | RH + Schoenfeld alone | Lean kernel |

The matched same-package comparison is 0.7803 vs 0.70 at exp(8), not 0.9848 vs 0.70 under identical inputs. Neither a new literature record nor an assumption-free proof of the source formulas is claimed. The 0.81/0.90/0.95 finite Büthe rows below also hold on the entire corresponding hybrid rays n≥45/4, 41, 161 respectively by the explicit `cube_hybrid_early` consumer. This whole-ray extension requires RH and Schoenfeld; the finite rows do not.

## Checked Chebyshev consumer
Writing N(a,b) for the number of natural primes p with a<p<b, for every real n≥369,
`N(n³,(n+1)³) > 0.96699 n²/log n` under ordinary RH, Schoenfeld's Theorem 10 (6.1), and Büthe's Theorem 2 (1.6)–(1.7). In particular this holds on the matched ray n≥exp(8). These are named input propositions in Lean, not new axioms nor Mathlib proofs of the papers. This route replaces the Green/Nicolas/BPT inputs with Schoenfeld and Büthe; the numerical improvement is not yet a same-package comparison. See `CubeTheta.lean`, theorem `CubeTheta.cube_exp8` and the earlier ray theorem `CubeTheta.cube_hybrid_096699`.

The Büthe-only finite slab, always capped by (n+1)^3 ≤ 10^19, gives coefficients 0.81 from 45/4, 0.90 from 41, and 0.95 from 161. These rows have no RH hypothesis. No finite source is extrapolated.

At any z strictly inside (a,b), the primes counted by θ(z) but not θ(a) belong to the strictly open window. Hence θ(z)−θ(a)≤N(a,b)log b. Pass a continuous lower envelope to the limit as z→b from the left; the upper bound at a is strict in both source applications. This avoids assuming b is composite or paying a gratuitous endpoint unit.

## Reproduction
```bash
cd /representation/source
/bin/lean -o /work/objects/QuarticWindow.olean QuarticWindow.lean
cd /work/submission
/bin/lean CubeTheta.lean
```
Create /work/objects first if absent. Lean prints the endpoint, consumer and headline axiom sets [propext, Classical.choice, Quot.sound]. The imported CompactDualVerified obstruction concerns a fixed Fourier functional at A=36/11, not cube counts or prime-gap impossibility. No actual C source-to-semantics result is claimed.

## Sources
- Schoenfeld, Math. Comp. 30(134), pp.337–360, Theorem 10 (6.1), printed p.337/PDF p.1. The actual offline `/corpus/literature/Schoenfeld1976.pdf` has SHA-256 `8c3cac1ee52eb05af05ec410adc587a18505a46aacdde41ae097038b0e7c3897`, 1795864 bytes, agreeing with the recovered pin in the addendum. Its stale quarantined-response filename annotation does not describe these bytes. The staged secondary predicate is used verbatim.
- Büthe, arXiv:1511.02032v2, Theorem 2 (1.6) and (1.7), printed/PDF p.2, `/corpus/literature/Buthe1511.02032v2.pdf`, SHA-256 `350f96313810ded3e8eaf2af6006b227c8834235e177f49eabb3d43d4931c4d1`. Historical rigorous computation is consumed as a source predicate; no new PV.
- Inherited comparator: `/representation/source/IEANTN/Nodes/PrimePowerPopulation/v1/Conclusions.lean`, `cube_density_all_real`; requires the octic family, originally RH and Green/Nicolas/BPT. Checkpoint improvement is on exactly the same real ray and with strictly open endpoints, under different named source inputs.

## Primary-paper range comparisons

- **Schoenfeld and Büthe:** The Lean transfer proves the full strict-open endpoint inequality in each paper's actual range (see `schoenfeld_raw`, `buthe_raw`), with no use of Büthe above its cap. Raw subtraction of right-continuous values would include b if it is prime. For Schoenfeld alone the matched exp(8) coefficient exceeds the inherited 0.70 with *different* analytic inputs, but falls below 0.7803; Büthe alone yields the stronger finite branch, not a ray.
- **Blanquer Robles** v2, 21 Nov 2026, Theorem 3, printed p.2/PDF p.2: the printed count uses (x,x+c*√x log x], c*=681/800, x≥4·10¹⁸. At x=n³, on its full cube-admissible range n≥(4·10¹⁸)^(1/3), the right endpoint is strictly inside the cube window, since √n/log n≥6.82 at n≥exp(8). The single-window numeric guarantee printed in that theorem is <2n√n there: log(c*log(x)log(2)/2)≤log x, κ>0, and (σ+β)/MW<2 in the printed notation. The matched cube guarantee 0.96699 n²/log n is >6n√n on this range. This only compares the **printed single-window guarantee after inclusion**, not retunings or every consequence of the paper. The earlier x≥4 existence assertion is not that quantitative count.
- **Blanquer Robles** Theorem 2 Eq. (2), printed p.2 and ordinary-modulus paragraph p.10: set q=1, so RH suffices. For α≥0 and c above the printed affine minimum, the eventual half-open population lower bound is α√x on unrestricted real x. In cubes, tile with common width c√b log b, b=(n+1)³, taking a floor and dropping one possible right-end prime per cell. For each fixed α,c, the liminf normalized cube coefficient obtained this way is at least α/c: width ratio √b log b/(√a log a)→1, the floor is negligible, and the dropped endpoints are negligible as a=n³→∞. The supremum from these printed affine lines by this argument is 1/1.505237 (about 0.66435), without an explicit onset. This is an asymptotic **guarantee comparison**, not a limit on their method or on actual primes. The direct Schoenfeld transfer in fact has cube lower coefficient 1−O((log n)²/√n), by the displayed errors and log-step inequality.
- **CMS** arXiv:1708.04122v2 Thm. 3 / Cor. 4 (gap reduction, fixed A=36/11), and **Blanquer Robles** Thm. 1 (asymptotic gap) are not fixed-onset prime-population statements. No finite onset, generalized RH claim, new Gaussian bound, or smaller exterior penalty is inferred. The compact dual import does not enter the Chebyshev or smoothing proofs.

See `WrittenExtensions.md` and the two exact-arithmetic scripts for the unchanged-package argument and both smoothed hybrids. Run the scripts with `/usr/bin/python3.10 -B`. Neither a successful script nor the ordinary Lean kernel arithmetic is actual-C-character-to-execution PV.
