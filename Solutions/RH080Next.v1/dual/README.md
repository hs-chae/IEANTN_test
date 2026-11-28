# Full-class CMS duality and finite prime-gap bridge

This is additive research on the frozen RH0.8 study. Original outcomes and inputs are preserved. No official Comparator receipt is claimed.

## Completed analytic proofs

- `AbelFourierInversion.lean`: actual Fourier inversion with a Gaussian cutoff, assuming only integrability of the original function and continuity at zero. The Fourier transform need not be integrable.
- `CMSWeakDuality.lean`: weak duality for the full real-even CMS class, including finite positive exterior leakage. The genuine Fourier transform is constructed from the original function. The reciprocal numerical bound has the correct lower-bound direction. All three standard Lean axioms only.
- `CoupledCMSObstruction.lean`: a finite nonnegative combination of the same CMS budgets retains a common dual obstruction. This does not rule out every different RH argument.
- `TangentKernel.lean`: monotonicity of sine divided by its argument and a global supporting-line inequality for the squared inverse cosine. The proposed polynomial numerical certificate using this inequality is not complete.
- `FinitePrimeGapBridge.lean`: the literal historical CMS(1.15) input gives an open prime interval at coefficient 0.74 for every real x from 11 through 4*10^18. Direct kernel proofs handle coefficient0.777 from4 to11. The resulting coefficient0.8 bridge includes every real x from4 through exp42; the overlap exp42<4*10^18 is proved. This does not establish the requested analytic extension through exp174.

The historical input is strict: consecutive-prime gap smaller than the square of the logarithm of the lower prime, for lower prime between11 and4*10^18. It is the published finite computation cited by [CMS, equation(1.15)](https://arxiv.org/abs/1708.04122v2), not a new independently verified numerical program.

## Actual-C source-first consequence

`SourceFirstCMSObstruction.lean` composes the new full-class proof with the preserved `RH080Study.v1/pv/dual_grid.c` source-first chain. Its intended theorem gives the exact functional floor100/123 on the full CMS class, and consequently excludes0.8 within this functional. The old C source, execution model and numerical cap are unchanged. The combined49-module source-cold replay **passed**, including all11exact theorem-identity and standard-axiom audits. It rebuilt every application dependency from source, without an application object-bank fallback. This is local Lean verification, not official Comparator acceptance.

The C compiler, ABI, documented libc output behavior, OS and hardware remain the stated physical execution boundary. This project does not formally prove those platforms correct. Functional obstructions do not constitute lower bounds on actual prime gaps.

## Stronger dual numerical result: explicitly outside Lean and PV

The published rational-step cap is1.20786, giving functional floor50000/60393. A new rationalized LP iterate in `inputs/dual-rh-generated-R10.json` gives cap1206951/1000000, hence floor1000000/1206951 (approximately0.82853404984958). Two actual directed-Arb verifiers have checked the global bound: a Fourier-transform grid plus curvature, and an independent complex-Horner adaptive chord calculation with4158intervals. They share Arb, but not the FFT algorithm. **The stronger numerical cap is not kernel-closed and is not source-first PV.** It has not been promoted into the verified network.

The original exchange LP later hit its per-LP time limit; this result comes from a preserved earlier iterate, not a claim of optimizer convergence or optimality. Larger-support and interior-point searches are ongoing. Every run uses explicit fresh receipts; negative controls exercise the real CLI in normal, `-O` and `-OO` modes.

## Reproduction

Prepare the exact pinned Lean and eight generic libraries as described in the preserved [baseline reproduction guide](../../RH080Study.v1/REPRODUCE_FINAL.md). No historical application object bank is allowed. From a checkout, run:

```sh
python3 Solutions/RH080Next.v1/dual/reproduce_dual.py \
  --repository /absolute/network \
  --context /absolute/pinned-generic-context.json \
  --run /absolute/fresh/full-cms \
  --workers 4
```

This builds every application dependency from source, including the independent C grammar and all sine/LeanCert mathematical dependencies, then audits11exact theorem identities and their axioms. A preflight uses `--check-only` and never produces mathematical acceptance. The pinned original `dual_grid.c` physical execution receipts remain in the baseline; this replay rebuilds its complete Lean source/AST/execution/real-integral consequence.

`FinitePrimeGapBridge.lean` is standalone over pinned Mathlib. Compile it using the same generic-only context with `lean -j1`, and inspect its four `#print axioms` lines. It is separate from the49-module dual audit.

For supplementary interval computations, use Python3.12.9 and python-flint0.9.0:

```sh
python3 replay_source_dual.py --witness inputs/dual-rh-generated-R10.json \
  --run /absolute/fresh/dft --panels 1048576
python3 verify_dual_adaptive.py --witness inputs/dual-rh-generated-R10.json \
  --run /absolute/fresh/horner --target 1.206951
python3 replay_controls.py /absolute/fresh/rejection-controls
```

The two interval scripts generate their numerical data deterministically. No random seed is used. Preserve their source hashes, plan/result receipts and the small compressed adaptive certificate. Large object banks and failed-run temporary arrays are regenerable; remove them only after a checked completed reproduction, keeping the sources and receipts.

## Reproduce the strongest existing external interval proposals

The previous R10 command is retained as historical context. The strongest
reported fixed proposals use `inputs/dual-rh-generated-m48-R60.json` and
`inputs/dual-a4-generated-m48-R60.json`, byte-identical to their original
recorded inputs. The strict supremum caps are respectively 2399/2000 and
5877/5000; their reciprocal functional floors are 2000/2399 and5000/5877.
The latter profile has leakage penalty 4, so it is a different functional from
the ordinary-RH 36/11 profile. These are external directed-interval numerical
results, not Lean numerical leaves, source-first PV, optimizer certificates,
or inputs promoted into the verified network.

Use Python3.12.9 with `python-flint==0.9.0` (see
`../reproduction/requirements-external-duals.txt`). The exact four-command
plan is produced without running any large numerical work by:

```sh
python3 ../reproduction/reproduce_external_duals.py \
  --python /absolute/path/to/python3.12.9 --run /absolute/fresh/dual-plan
```

Run that same wrapper with `--execute` and a different fresh output directory
to regenerate the four results. It pins every witness, verifier and common
helper hash before execution and checks the distinct final result kinds.
Both DFT replays use 16777216 panels at 128 bits. Both independent non-FFT
complex-Horner replays use 3008 bits, the original 32 initial intervals and
maximum depth 30. No optimizer or random seed is used. Successful output
includes the newly generated compressed adaptive certificates and their
hashes; preserve them together with PLAN/RESULT/source records.

Earlier 160-bit Horner attempts did not produce acceptance; their executed
sources/plans remain historical evidence. The later higher-precision result
does not retroactively convert those attempts into successes. In particular,
a wide interval enclosure is not a counterexample to the target cap.
