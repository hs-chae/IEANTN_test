# Ramanujan source-first PV research

**Status: active research; the full finite source-first execution is not closed.**
Read [the offline HTML report](reports/RESEARCH_PROGRESS.html) and the machine-readable
obligation inventory. A passing native run is not a completed Lean numerical theorem.
No existing IEANTN conclusion, frozen experiment outcome or official justification
has been changed. These build/run records are research records, not official
verification-workflow receipts.

## Mathematical target and current results

The target concerns the actual prime-counting function, for every real
`x >= 38,358,837,683`. The desired inequality is rendered in the HTML report.

* The actual optimized **C quotient counter** is proved to terminate and return
  `Nat.primeCounting N` for every `2 <= N <= 2e12` under its proved caller-buffer
  conditions. Exact bytes, typed AST, source initialization, ascending/descending
  loops, outer loop, sqrt helper, arithmetic and pointer applicability are covered.
  Every completed modeled function execution has that result. The older uint64
  trial counter is also proved, but is an inefficient numerical proof strategy.
* The actual fixed-input C main has source-bound static initialization and stateful
  operational semantics. Its complete successful execution is constructed, and
  **every modeled main execution returning zero** writes exactly the actual count.
  Both stdio failure branches are retained. Physical GCC/ABI/stdio/OS/hardware
  applicability and the particular count numeral remain separately evidenced.
* A closed kernel quotient certificate proves `pi(1,000,000) = 78,498` and supplies
  the numerical result to that source-function theorem. The full target is much larger.
* The full finite prefix through `1,490,000,000,000` has **ordinary**, independently
  checked numerical coverage: 1,755,663 cells, 98,317,128 certificate bytes. A
  completely separate byte sieve checks every count, and an independent 96-bit
  logarithm algorithm checks every enclosure. The full source-first consumer is open.
* The analytic continuation on the closed interval from `1.49e12` through `1e19`
  is proved in Lean under the named Büthe/Axler and special-function inputs.
  It reduces the computational interval length by about 8.22% against Axler's
  `1.62e12` transition. Endpoint positivity is proved, never assumed.
* `FinalAnalytic.quantitative_from40` now proves the actual-prime-count margin
  throughout the entire closed ray `x >= exp(40)`, with the exact original sixteen
  QRH/density inputs plus six named analytic/normalization inputs. The 655 existing
  dependency modules were freshly rebuilt. The two-sided pi expansion is derived,
  not assumed as an extra external input. `FinalAnalytic.analytic_ray` adds the
  theta deficit and Axler lower bound and closes all real `x >= 1.49e12`.
* The first critical 56 real units, the preceding integer counterexample, and a
  recovered uniform first-cell margin greater than `52,869,788` have compiled
  consumers requiring only the same two large source-linked counts. The numerical
  certificate for those counts is undergoing actual large kernel checks; its
  completion must be checked before these are called unconditional numerical results.

* The new segmented C checker has source/AST correspondence, mathematical
  classification/count-increment proofs, and a complete actual initialization loop.
  Its divisor/stride and final checking/counting source loops remain in progress;
  native million-word differential tests are ordinary evidence.

The report distinguishes source-first program verification, kernel numerical
certificates, ordinary numerical checks and literature-supported analytic inputs.
No `native_decide`, new axioms or `sorry` are permitted in the selected new proof chain.

## File map

`c/verified_primecount.c` is the source-bound trial counter. `CSource`, `CArithmetic`,
`PrimeCount` and `CheckerExecution` supply its identity, operational and mathematical
proofs. `QuotientSieve` and `QuotientAlgorithm` prove the optimized counting recurrence;
`QuotientTables` proves the actual ascending/descending table algorithm.
`QuotientOptimized1000000` is the completed generated numerical proof.
`QuotientCSourceV2` through `QuotientCFunction` prove the actual optimized C source.
`QuotientDriverSource`, `QuotientDriverInit`, `QuotientDriverExecution` and
`QuotientDriverSuccess` cover the fixed-input standalone application.
`QuotientCCell` connects actual source executions to the existing certificate.

`c/generate_finite.cpp` is the **untrusted** full finite generator, backed by
primecount/primesieve. `c/independent_finite_check.cpp` independently checks all
counts with its own byte sieve and quotient anchors. `c/benchmark_quotient_pi.cpp`
is a separate counting implementation. None of these native checks alone is PV.

`Intervals`, `AnalyticTransition`, `QuantitativeTail`, `EarlyMiddle` and `AnalyticGlue` prove actual
real interval transport, the stronger analytic transition and the final conditional
assembly. The exact seven-word binary format maps to the existing certificate type.
`QRHFullTail` derives the exact existing pi expansion from its original sixteen
inputs. `FinalAnalytic` closes the analytic ray and the conditional final assembly.
`FirstCriticalCell` and `RecoveredMargin` reuse the same two source-count outputs
for a local interval, quantitative margin and preceding integer counterexample.

`audit/` preserves actual Lean commands, source/compiler hashes, outputs, resources
and failed attempts. Experimental benchmark modules are not all intended as default
build roots; the documented selected roots identify the accepted claims. Do not
infer proof acceptance merely from a `.lean` file existing.

## Clean numerical reproduction

Use Linux x86-64, Python 3.11, GCC/G++ 11.4, CMake and Git. The recorded machine
has 128 available logical CPUs and more than 1 TiB of genuinely available RAM;
RAM and free disk were checked separately. The native algorithms themselves use
much less memory; recorded per-process limits are ceilings, not reservations.
The current fixed host harness checks a 512 GiB available-memory reserve and 1 TiB
free disk before full dispatch. It uses CPUs 16–31 and 32–47 for matched native
runs, and 48–55 for the independent exact enclosure checker. Run on a compatible
host or explicitly adapt these harness choices and record the new conditions.
Do not change the mathematical range, algorithms or enclosure parameters.

From this directory, choose **two fresh output directories** on adequate storage:

```sh
python3 scripts/reproduce_numerics.py \
  --scratch /adequate-disk/fresh/ivy-ramanujan-source-pv-20261119 \
  --study /adequate-disk/fresh/study
```

The script clones primecount at exact commit
`9eb78bc0d1c98129f464db287699532376f52950`, builds it and bundled primesieve,
builds the actual sources, runs the entire finite generator, checks all exact
cell inequalities/enclosures and exhaustively checks every prime count.
`--end 1620000000000` reproduces the older transition; `--mode unit` reproduces
the conservative unit-increment baseline. Both algorithms retain identical inputs,
64 chunks and 16 workers. No random seed is used.

The complete clean reproduction is an ordinary numerical result. Its receipts
cannot be substituted for a source-first execution theorem. All certificate files
are deterministic; per-chunk SHA256 values enable a byte-exact comparison.

The stricter V2 wrappers additionally validate the complete fixed chunk universe,
source/executable identities and strict JSON parsing, and remain effective under
Python `-O` and `-OO`. V1 source identities and historical runs are preserved.

## Fresh Lean reproduction

Pins: `leanprover/lean4:v4.34.0-rc2`, Lean commit
`6a10ac8c22beadecabdbb0919c2b50214762f91d`, Mathlib
`71a80585ee495fc24472fd0eaffc89d94e4fd8d6`.
`BUILD_CONTEXT.json` records all eight actual generic dependency revisions and the
exact Linux compiler hash. The optional historical Cli package was absent and is
not used by the selected imports. Never mix objects from other Lean versions.

On a clean clone of this branch, install Elan and the pinned toolchain, then run
`lake exe cache get` from the repository root using its existing pinned manifest.
Do not run an unconstrained dependency update. This obtains the same generic
Mathlib dependencies; **no old application proof objects** may enter the replay.

```sh
python3 scripts/bootstrap_context.py --out CLEAN_CONTEXT.json
python3 scripts/reproduce_lean.py --context CLEAN_CONTEXT.json \
  --out /adequate-disk/fresh/lean-replay
```

The helper resolves the selected imports, validates each generic source commit,
builds every application object into a fresh directory and records actual commands,
source hashes and GNU-time output. Original-machine replay can use
`--context BUILD_CONTEXT.json` directly. Select CPU affinity with `--cpus` when the
original 0–3 set is unavailable.

The million-input numerical proof is intentionally substantial:

```sh
python3 scripts/reproduce_lean.py --context CLEAN_CONTEXT.json \
  --out /adequate-disk/fresh/million-replay \
  --root RamanujanPV.QuotientOptimized1000000
```

Its deterministic generator is `scripts/generate_optimized_quotient_proof.py`.
Additional accepted program components can be selected with repeated `--root`.
The targeted historical QRH closure has its own `scripts/rebuild_qrh_closure.py`:
it rebuilds existing dependent solutions from pinned source, records the full
module map and checks the final theorem's actual axioms. Literal native-related
text in an unused generic tactic is not itself a native dependency of a theorem.

## Source evidence and remaining trust

The report gives exact theorem/equation/page locators. Source manifests preserve
PDF hashes and versions; research-library originals stay outside publishable source.
Büthe, Axler, CH2, Dusart and the precise special-function normalization/series
statements remain explicit analytic inputs where not rederived. Their underlying
published computations are not claimed source-first verified here.

Remaining native observations rely on the recorded compiler/ABI, runtime, OS and
hardware. The selected formal source-function subset models its own control flow,
unsigned arithmetic and helper bodies; it does not prove all of GCC or the OS.
Lean proofs use only the reported standard logical axioms. The modeled main/output
connection is now proved; the final full finite numerical execution/certificate
remains an explicit open obligation. Check `evidence/SELECTED_PROOF_INVENTORY.json`
for exact selected declaration identities, current source hashes and actual audits.
That inventory is a hand-enumerated integration scope, not an exhaustive source-claim
audit of the entire IEANTN repository.

## Storage

Do not retain full prime lists. Preserve sources, exact parameters, hashes,
essential proof/certificate evidence, failed attempts and build/run records.
After actual regeneration and comparison pass, large certificate duplicates,
compiler caches and scratch can be removed **only** using a reviewed list of
experiment-owned paths. Accepted proofs and original locked inputs must not be
removed as generic scratch. Cleanup receipts describe any deletion actually done.
