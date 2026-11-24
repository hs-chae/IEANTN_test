# Reproduce the one-prime analytic work

The proved outputs are conditional on `RiemannHypothesis` and the new, explicitly named `RHOnePrime.CMSPrime.SourceCMS616` literature proposition. It is the published CMS equation (6.16), with its actual cosine kernel, not a formalization of that equation from the inherited Green/Nicolas/BPT interfaces. `SOURCE_MAP.json` identifies the primary proof passage. No new axiom or admission supplies it.

The strongest formal interface is `RHOnePrime.CMSContinuous.open_prime_continuous` in `CMSContinuousFrontier.lean`. It retains the complete logarithmic profile and proves a strict-open interval whose endpoint is uniformly below the coefficient .8768 window. Separate finite-domain consumers give .8185 through exp(59), .8357 through exp(110), and .8512 through exp(225), all starting at exp(44). The .8357 statement is bounded; it is not an asymptotic record. `ANALYTIC_HANDOFF.json` lists exact written identities, source hashes and proof boundaries.

## Lean proofs

Use the parent campaign's reproducibility instructions to produce its pinned Mathlib/LeanCert foundation and `GENERIC_CONTEXT.json`. Lean is 4.34.0-rc2 and Mathlib is 71a80585ee495fc24472fd0eaffc89d94e4fd8d6. Then run:

```
python3 analytic/reproduce_frontier.py \
  --context /pinned/GENERIC_CONTEXT.json \
  --foundation-paths /pinned/foundation/objects \
  --out /fresh/frontier
```

Run from `Solutions/RHOnePrimeEvolution.v1`. The output must be new. The script copies all thirteen sources before compiling, compiles every new module in dependency order, checks all printed headline axiom closures against the standard three axioms, and records exact commands, compiler/source/object/log hashes, elapsed time and actual GNU per-child RSS. It explicitly reuses the supplied generic foundation and does not claim a fresh rebuild of that foundation. The actual local accepted run is `evidence/fresh-all13-v1/RESULT.json`: 66.01 seconds, 63 printed axiom closures and no native execution axiom. The parent campaign's broader fresh transitive replay is separate evidence.

The older scoped runs and first nine-module checkpoint remain preserved. Their initial helper's fixed `PASS_SCALAR_ONLY` label was stale for later prime consumers; actual theorem-type and axiom output, followed by the source-frozen thirteen-module replay, establish the final proof status.

## External numerical research

These calculations are explicitly external arithmetic (tier E). They are not source-first program verification, Lean-kernel verification, or accepted numerical premises in the verified network. The scalar objective is not by itself an RH prime theorem.

Create an isolated CPython 3.12.9 environment and install:

```
python-flint==0.9.0
sympy==1.14.0
```

The exact seeds under `seeds/` and the exact integer hat witnesses under `hat-witnesses/` are essential small reproducibility inputs. No random seed is used. The mathematical claims depend on these pinned data, not on the floating solver reproducing identical optimizer choices.

```
/path/to/python analytic/external_controls.py --python /path/to/python --out /fresh/controls

/path/to/python analytic/external-certifiers-frozen-v1/certify_gaussian_objective.py \
  --candidate analytic/seeds/A36over11-degree40.json \
  --A 36/11 --out /fresh/gaussian40

/path/to/python analytic/external-certifiers-frozen-v1/check_fourier_gaussian.py \
  --candidate analytic/seeds/A36over11-degree20.json \
  --out /fresh/fourier

/path/to/python analytic/external-certifiers-frozen-v1/certify_hat_witness.py \
  --witness analytic/hat-witnesses/asymp-m200.json \
  --grid 1048576 --out /fresh/hat-asymptotic

/path/to/python analytic/external-certifiers-frozen-v1/certify_hat_witness.py \
  --witness analytic/hat-witnesses/explicit-m100.json \
  --out /fresh/hat-explicit
```

The first command actually passed fifteen positive/negative CLI routes across normal Python, `-O` and `-OO`, comparing numerical results. The Gaussian proof outline uses exact rational Sturm root isolation and complete Gaussian primitive recurrences, including infinity limits. A separate monomial/Hermite transform calculation and seven direct complex-Arb cosine integrals check the Fourier normalization. These do not constitute a Lean proof of the analytic identities.

The new degree-40 Gaussian objective at multiplier 36/11 has externally enclosed inverse 0.8339488676671668. The new exact hat witness at multiplier 36/11 has externally enclosed ratio below 0.833967358. The multiplier-4 hat witness has ratio below 0.851116467. These improve the compared scalar objectives numerically. They remain outside the verified network: actual FFT-to-trigonometric-sample and periodization proof obligations have not been closed. The 2026 source supplement's own analytic bridge also assumes those identifications; its finite FFT arithmetic must not be mistaken for a completed norm proof.

## Reproduce exploration and negative results

The original floating LP search used CPython 3.11.14, NumPy 2.4.4 and SciPy 1.17.1. Run `search_gaussian.py` with degree list `4,8,12,20,28,40` and `--A 4`, or `8,12,20,28,40,60` and `--A 3.2727272727272727`. Exact generated decimal seeds are preserved. `screen_kernels.py` and `screen_mixtures.py` explore compact polynomial, tent, cosine, Box, asymmetric, mixture and bandlimited candidates. These screens have no certificate status.

The bounded SOS trial used CVXPY 1.7.3, Clarabel 0.11.1, SCS 3.3.2, NumPy 2.5.5 and SciPy 1.18.1. The Clarabel run failed; the 10,000-iteration SCS run returned bad PSD eigenvalues and a large coefficient residual. No rational PSD certificate was accepted. Its source is `try_sos_norm.py` and the negative evidence is retained.

`MISTAKES.md` records corrected reasoning, exploratory quadrature failures, stale status labels and the source/run association correction. Source-bound historical outcomes remain unchanged. All retained evidence is small; numerical arrays and optimization workspaces live only in process memory. Do not delete the parent campaign's accepted proof banks or original sources during cleanup.
