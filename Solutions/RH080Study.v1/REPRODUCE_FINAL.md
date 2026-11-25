# Reproducing the final RH0.8 study

This is the final coverage guide. Start with the single [research report](reports/RH080_COMPLETE_REPORT_EN.html), then use this file together with the original [REPRODUCE.md](REPRODUCE.md). The original guide and `reproduce_study.py --lane all` intentionally retain their **frozen 278-input scope**. They do not include the later cube-from-369 proof, finite-frontier nodes, three-formula competition figure, or the new written/external followup results. There is no `reproduce_study_all.py` executable.

The complete cold component proofs below actually ran. The relocated numerical-regeneration and scalar wrapper routes also actually ran. **No monolithic full `--lane all` wrapper run, and no single wrapper covering all later additions, was executed.** A preflight or an accepted individual child is not evidence of such an end-to-end run. This document supplies the exact separate commands and points to their actual receipts; it does not change that history or the original experimental outcomes.

## 1. Restore sources and prepare the pinned generic libraries

Use the delivered verified source archive or a checkout at the report's displayed source revision. For archive verification/extraction, follow [release/README.md](release/README.md), using the separately delivered whole-archive SHA256. Read that source revision from the report; do not advance dependencies to a later branch tip. All application mathematical source inputs needed by the completed proof routes are included or deterministically regenerated. External Lean/package binaries and repositories are infrastructure and must be provisioned separately. Literature-backed source statements remain explicit mathematical assumptions; the package does not reprove RH or the historical prime-gap/zero computations, and it does not distribute every original paper.

The compact archive omits exactly 49 generated Gaussian cell source modules. A full Git checkout may already contain them. From either layout, use the same safe materializer before the mathematical wrapper:

```sh
python3 -OO /absolute/network/Solutions/RH080Study.v1/materialize_generated.py \
  --repository /absolute/network \
  --scratch /absolute/fresh/cell-bootstrap
```

`GENERATED_CELL_SOURCES.json` lists all 49 exact paths/hashes; `REPRODUCTION_INPUTS.json` fixes the 278 original inputs. The materializer restores missing files, rejects an existing different file, verifies all 278 hashes, and removes its verified regenerable arrays after success. `--check-only` reports missing sources without materializing them. Actual compact restoration took 94.55 seconds and passed the all-mode controls. Source regeneration is not proof acceptance.

For the core routes, use Linux x86-64, Python 3.11 (the study interpreter was 3.11.14), Git, GNU `time`, `prlimit`, GCC/C11, Elan and the pinned Lean toolchain. The accepted C compiler was GCC 11.4.0. Lean must be 4.34.0-rc2, upstream commit `6a10ac8c22beadecabdbb0919c2b50214762f91d`, with executable SHA256 `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`. Use the actual `bin/lean` binary, not the differently hashed Elan launcher. Exact generic package commits are in [estimates/DEPENDENCY_PINS.json](estimates/DEPENDENCY_PINS.json) and the repository's `lake-manifest.json`; Mathlib is `71a80585ee495fc24472fd0eaffc89d94e4fd8d6`.

From the repository root, the ordinary infrastructure setup is:

```sh
elan toolchain install leanprover/lean4:v4.34.0-rc2
lake exe cache get
```

Keep the pinned manifest; do not run `lake update` to select new revisions. If the generic cache is unavailable, compile those same pinned generic packages from source. The eight reused libraries must occupy `.lake/packages/<package>/.lake/build/lib/lean`, with their tracked Git sources clean and `.git` revisions available for checking. No historical IEANTN application object bank is a prerequisite for the cold routes below. The core mathematical replay does not need NumPy, SciPy, python-flint or a model account.

Use a fresh experiment-owned directory outside the repository for every `--run`, `--out`, `--output`, `--scratch` or receipt destination. Substitute real absolute paths in the examples; never copy historical `/data` paths as if they existed on a clean machine. The wrapper generates `/absolute/fresh/original-study/generic_context.json`; all later commands can reuse this checked **generic-only** context.

## 2. Original frozen components and their actual coverage

The following is the complete original-scope recipe, with controls enabled:

```sh
python3 -OO /absolute/network/Solutions/RH080Study.v1/reproduce_study.py \
  --repository /absolute/network \
  --compiler /absolute/toolchains/leanprover--lean4---v4.34.0-rc2/bin/lean \
  --packages /absolute/network/.lake/packages \
  --lane all \
  --run /absolute/fresh/original-study
```

This exact all-lanes recipe is **not itself an executed monolithic success receipt**. Its child components were executed separately and closed. Add `--check-only` with a different fresh run path for source/tool/context/child-CLI preflight only; it publishes `PREFLIGHT.json`, never mathematical success. To use an existing checked generic context, supply `--context /absolute/context.json` instead of both `--compiler` and `--packages`.

| Included original component | Actual proof boundary |
|---|---|
| `pv/reproduce_joint.py`, then `pv/reproduce_canonical.py` | 45-source actual C/source-AST/execution/analytic chain and eight-file canonical append; source-first PV for the stated scalar fragment |
| Original cube and zero-count envelope | 15-source full cube consumer; separate exact Bellotti–Wong/BPT transport and minimum consumer |
| Same-source cube 0.78146 from exp(8) | Complete whole-real tiling under the unchanged original Octic input family |
| Pareto cube 0.9669924 from exp(8) | Complete source-conditional consumer retaining the original 0.965/exp(6) conclusion |
| G80 and original-input G56 Fourier/ANT consumers | Each full 80-module cold closure, all cells, true Fourier transform, both infinite tails and actual CMS/RH consumers |

These mathematical Lean routes are kernel proofs with declared analytic premises; the Gaussian computations are not source-first PV. The original [REPRODUCE.md](REPRODUCE.md#exact-constituent-routes) gives each child CLI explicitly, including four Gaussian workers, 32GiB per worker, and the repository-contained LeanCert source provider. No old application bank or `--reuse-cold-leaves` shortcut is used by the complete cold recipe.

The wrapper's `--lane numerics` separately regenerates all sine source files, both Gaussian cell partitions, rational Fourier source transforms, the C AST/source representation, and the actual compiled C output. That relocated route actually ran and preserved its receipts in `reproduction-evidence/relocated-numerics-final-v1/`. It is numerical/source regeneration, not a replacement for the Lean consumers. `--without-controls` records controls omitted and must not be called the full checked procedure. `--include-baseline` optionally adds the 300-source predecessor and 53-source predecessor-Gaussian packets; it preserves their historical outcomes.

## 3. Later completed kernel additions: run separately

These commands cover the final additions that the 278-input wrapper deliberately excludes.

**Exact timely cube source, every real n ≥ 369, and the v2/v3 hybrid:**

```sh
python3 /absolute/network/Solutions/RH080Study.v1/estimates/early369/reproduce.py \
  --repository /absolute/network \
  --context /absolute/fresh/original-study/generic_context.json \
  --run /absolute/fresh/early369
python3 /absolute/network/Solutions/RH080Study.v1/estimates/early369/test_controls.py \
  --context /absolute/fresh/original-study/generic_context.json \
  --objects /absolute/fresh/early369/objects \
  --run /absolute/fresh/early369-controls
python3 /absolute/network/Solutions/RH080Study.v1/estimates/early369/test_reproduce_cli.py \
  --context /absolute/fresh/original-study/generic_context.json \
  --run /absolute/fresh/early369-cli-controls
```

The complete 53-source closure actually passed under normal Python, `-O` and `-OO`, as did 18 actual Lean controls and 39 CLI controls. Repeat the first two commands with each optimization flag and distinct fresh directories to reproduce those modes; the CLI suite itself tests all three. The exact submitted source bytes, canonical adapters, actual input use, strict-open endpoints, natural onset 369 and retained 0.9669924/exp(8) hybrid are pinned in [estimates/early369/README.md](estimates/early369/README.md), `INPUT_MANIFEST.json` and `VERIFICATION_SUMMARY.json`. Ordinary RH, Schoenfeld's refined theta clause and Büthe's two finite theta clauses remain explicit source inputs. This later canonical integration does not retroactively change any trial outcome.

**Finite real-input frontier, without RH:**

```sh
python3 /absolute/network/Solutions/RH080Study.v1/finite_frontier/reproduce.py \
  --root /absolute/network \
  --context /absolute/fresh/original-study/generic_context.json \
  --run /absolute/fresh/finite-frontier
python3 /absolute/network/Solutions/RH080Study.v1/finite_frontier/test_controls.py \
  --context /absolute/fresh/original-study/generic_context.json \
  --accepted /absolute/fresh/finite-frontier \
  --run /absolute/fresh/finite-frontier-controls
```

This actually rebuilt all 12 source modules and checked all eleven roots. Its control command repeats the whole closure under `-O` and `-OO`, then exercises malformed/reuse and Lean premise/domain controls. The result stops at the exact certified terminal prime 18446744073709551557, not at every real number below 2⁶⁴. The log-squared branch and minimum-width hybrid retain the named historical gap-computation assumptions; they do not regenerate those historical prime sweeps. See [finite_frontier/README.md](finite_frontier/README.md).

**Three-formula population competition, scalar proof and figure only:**

```sh
python3 /absolute/network/Solutions/RH080Study.v1/reports/reproduce_competition_scalar.py \
  --context /absolute/fresh/original-study/generic_context.json \
  --run /absolute/fresh/competition-scalar
python3 -m pip install --target /absolute/fresh/render-packages matplotlib==3.10.7
python3 /absolute/network/Solutions/RH080Study.v1/reports/plot_population_competition.py \
  --render-package /absolute/fresh/render-packages \
  --out /absolute/fresh/competition-figure
python3 /absolute/network/Solutions/RH080Study.v1/reports/test_competition.py \
  --context /absolute/fresh/original-study/generic_context.json \
  --render-package /absolute/fresh/render-packages \
  --run /absolute/fresh/competition-controls
```

The exact 11-root scalar comparison and normal/`-O`/`-OO` controls actually passed. The SVG/PDF use font paths; CSV/JSON preserve exact rational curves and crossings. This compares the stated G56, published-2026 and Octic formulas with their distinct source packages/onsets. It is not a new ANT transfer or a global optimum. Matplotlib's ordinary rendering dependencies do not enter a numerical theorem. See [reports/POPULATION_COMPETITION_README.md](reports/POPULATION_COMPETITION_README.md).

## 4. Written/external followup results: optional numerical adjudication

These independently checked results are **E**, not completed Lean ANT theorems or source-first PV. They are not inserted into the verified canonical network. Numerical checks do not replace the written source-applicability, whole-continuum, finite-join and strict-endpoint arguments in their reviews.

The independent complete global-chord route needs only the standard-library Python runtime and the included exact coefficients and pinned FFT/twiddle engine:

```sh
python3 /absolute/network/Solutions/RH080Study.v1/ablation/followup/independent-global-chord/reproduce.py \
  --run /absolute/fresh/explicit-global-chord
python3 /absolute/network/Solutions/RH080Study.v1/ablation/followup/independent-global-chord/review_profiles.py \
  --run /absolute/fresh/explicit-profiles
python3 /absolute/network/Solutions/RH080Study.v1/ablation/followup/independent-global-chord/test_controls.py \
  --run /absolute/fresh/explicit-controls
```

The first command actually recomputed both dense norms, including 16,777,216 samples for the new w4 ray. It supports the written strict width 0.8 on [4,exp(174)] and width 0.851062 on the entire real ray from 4, with explicit named analytic/finite-computation inputs. `--slab-only` is a labeled subset. The profiles command recomputes the Fap norm at 524,288 samples and checks the other recorded profiles. The controls run three fresh slab/profile checks and three ray applicability rechecks of the included full-run receipt; they do not claim three fresh dense ray computations. Exact procedures and shared-engine trust are in [independent-global-chord/README.md](ablation/followup/independent-global-chord/README.md). The new all-parameter weighted population line is a separately recorded **written algebraic corollary** of these regenerated w4 norm/node inputs: [W4_POPULATION_CURVE_E.json](ablation/followup/evidence/W4_POPULATION_CURVE_E.json) states the exact rational derivation and required support-seven extension. It is not a further Lean/PV result.

For the curated cube certificate, run the optimization-safe evaluator against the exact captured prefix:

```sh
python3 /absolute/network/Solutions/RH080Study.v1/ablation/followup/reproduction/replay_rational_checks.py \
  --prefix-dir /absolute/network/Solutions/RH080Study.v1/ablation/followup/timely-prefixes/cube-L2_E2_D1_V1-r1/prefix-0002 \
  --trial cube-L2_E2_D1_V1-r1 --prefix prefix-0002 \
  --script scalar_checks.py --script sinc_certificate.py --script finite_cover.py \
  --mode normal --run /absolute/fresh/cube-external
```

Repeat with `--mode O` and `--mode OO` in fresh directories. The complete 196608-cell late sinc certificate and finite bridge actually passed in all three child modes; portable stdout equals the historical replay byte for byte. The helper checks LOCK hashes, makes assert guards explicit without changing arithmetic, rereads source/controller identities, and atomically publishes its receipt. It is ordinary exact-rational evidence, not formal Python execution semantics. The same helper covers the other curated last prefixes:

| Trial | Prefix | Exact `--script` arguments |
|---|---|---|
| cube-L2_E2_D1_V0-r0 | prefix-0003 | `--script cube_sieve.py` |
| cube-L2_E2_D1_V0-r1 | prefix-0005 | `--script scalars.py --script notches.py` |
| cube-L2_E2_D1_V1-r0 | prefix-0003 | `--script exact.py` |

Change both prefix directory and trial/prefix labels accordingly. The failed V1r0 Lean files are preserved unrepaired; their numerical/written results must not be relabeled as complete Lean proofs. Optional focused compilation in [reproduction/README.md](ablation/followup/reproduction/README.md) requires the exact assigned historical source/provider banks and is not an automatic clean bootstrap. The clean 53-source early369 route above independently reproduces the strongest accepted timely cube theorem without those banks.

**Arb/Gaussian and additional explicit/trapezoid adjudication require a separate flint environment.** The actual checked environment was Python 3.12.9, python-flint 0.9.0 and Sympy 1.14.0, recorded in [MATH_CHECK_ENVIRONMENT.json](ablation/followup/evidence/MATH_CHECK_ENVIRONMENT.json). Provision those exact versions in a fresh virtual environment; substitute its absolute interpreter path below. The core Python 3.11 environment has no flint requirement, and these Arb-dependent modules cannot even import there without flint.

```sh
python3.12 -m venv /absolute/fresh/flint-env
/absolute/fresh/flint-env/bin/python -m pip install python-flint==0.9.0 sympy==1.14.0
/absolute/fresh/flint-env/bin/python -OO /absolute/network/Solutions/RH080Study.v1/ablation/followup/verify_gaussian_artifacts.py \
  --audit /absolute/network/Solutions/RH080Study.v1/ablation/followup/evidence/FOLLOWUP_REAUDIT_normal.json \
  --reference /absolute/network/Solutions/RHOnePrimeEvolution.v1/analytic/external-certifiers-frozen-v1/certify_gaussian_objective.py \
  --python-flint /absolute/fresh/flint-env/bin/python \
  --curated-root /absolute/network/Solutions/RH080Study.v1/ablation/followup/timely-prefixes \
  --out /absolute/fresh/gaussian-adjudication
/absolute/fresh/flint-env/bin/python -OO /absolute/network/Solutions/RH080Study.v1/ablation/followup/verify_explicit_arithmetic.py \
  --submitted /absolute/network/Solutions/RH080Study.v1/ablation/followup/timely-prefixes/functional-L2_E2_D1_V0-r1/prefix-0003 \
  --certificates /absolute/network/Solutions/RH080Study.v1/ablation/followup/independent-global-chord/inputs \
  --out /absolute/fresh/explicit-arithmetic
/absolute/fresh/flint-env/bin/python -OO /absolute/network/Solutions/RH080Study.v1/ablation/followup/verify_trapezoid_arithmetic.py \
  --submitted /absolute/network/Solutions/RH080Study.v1/ablation/followup/timely-prefixes/cube-L2_E2_D1_V1-r1/prefix-0002 \
  --out /absolute/fresh/trapezoid-arithmetic
```

Ensure `python3.12` is the documented 3.12.9 interpreter when matching the recorded environment exactly. The Gaussian evaluator checks exact input/Fourier association, Sturm root counts and directed Arb antiderivatives/infinite limits. Its nine cases include eight passing submitted target comparisons and one **unclaimed reduced-penalty probe that does not establish 0.8**; process completion is not nine accepted targets. The helpers consume the published pinned reference/curated packets; they are not universal certifiers for arbitrary replacement references. No new research-model inference is needed for any command in this section.

The original two-curve scalar figure and the completed alternative-budget diagnostics are also separate auxiliary lanes, excluded by the original `--lane all`. With the same checked generic context and the flint interpreter prepared above:

```sh
python3 /absolute/network/Solutions/RH080Study.v1/reports/reproduce_scalar.py \
  --context /absolute/fresh/original-study/generic_context.json \
  --run /absolute/fresh/original-figure-scalar
python3 /absolute/network/Solutions/RH080Study.v1/functional/alternatives/reproduce.py \
  --context /absolute/fresh/original-study/generic_context.json \
  --flint-python /absolute/fresh/flint-env/bin/python \
  --out /absolute/fresh/alternative-budgets
```

The first is only a scalar comparison. The second reproduces its Lean scalar/whole-ray budget statements and external Arb diagnostic, with source-parameter extensions still labeled written/conditional. A negative sufficient budget is not a prime-free interval; a hypothetical reduced leakage penalty is not an applicable stronger RH theorem. See [functional/alternatives/README.md](functional/alternatives/README.md). Neither auxiliary route supplies a missing uniform 0.8 prime-gap theorem.

## 5. Actual costs, trust and storage

| Completed run | Actual observed cost; do not confuse scopes |
|---|---|
| C source-first joint closure | 935.1 seconds; maximum process RSS 101335824KiB, about 96.64GiB; eight-file canonical append separately about 23.2 seconds |
| G80 full cold 80-module consumer | About 1019.1 seconds; maximum process RSS 8181792KiB; sampled aggregate about 39.87GB |
| G56 full cold 80-module consumer | 797.48 seconds; maximum process RSS 5332212KiB; sampled aggregate 18358378496 bytes |
| Early369 full cold 53-module consumer | 179.79 / 176.57 / 176.17 seconds in normal/-O/-OO; maximum process RSS up to 4406528KiB |
| Finite-frontier full cold 12-module consumer | 47.64 seconds; maximum child RSS 6890048KiB |
| New competition scalar proof | 2.93 seconds in the normal run; maximum process RSS 3412564KiB; rendering/controls separate |
| Independent complete global-chord replay | About 119.95 seconds; peak process RSS 2872480KiB; no OOM/kill, about 318KB retained concise evidence |
| Final ordinary 12-project Lake build | 58.37 seconds on the prepared study host; a genuine incremental packaging build, not a cold union proof replay |

See each component's exact PLAN/RESULT, source and artifact hashes, GNU timing files and independent reviews. The receipts distinguish maximum individual process RSS, sampled process-tree totals, final directory bytes and unmeasured peak disk. No exact physical-host peak is inferred from a sum of shared RSS. These measured component times are not a measured monolithic runtime.

Check RAM and free disk independently. The original Gaussian admission expects at least 1TiB available RAM/free disk where its frontends require them; this is capacity admission, not a claim that the replay consumes 1TiB. Keep at least 256GiB host RAM in reserve. The original wrapper sequences its large jobs; its C execution proof has a 256GiB allowance and Gaussian workers normally have 32GiB each. New finite/global-chord runs require more than 320GiB available RAM, retain a 256GiB reserve and allow 64GiB per child. Early369 permits 32GiB per compiler. Do not run several full wrappers concurrently or impose the obsolete 4GiB ceiling. Preserve the separately authorized maximum 300GiB per experiment and 300GiB shared scratch ceiling when applicable; free disk never substitutes for RAM.

Preserve original sources, locked inputs, accepted proof/source/object artifacts, concise receipts and hashes. After checking an actual completed run, preview only its own regenerable scratch. The original [REPRODUCE.md](REPRODUCE.md#resource-policy-and-evidence) documents `cleanup_reproduction_scratch.py` and the checked approximately 1.025GB cleanup. Do not delete a checkout, unrelated directory, locked source, irreplaceable certificate or the only evidence copy. New finite/early369 proofs generate no prime lists or large numerical datasets; global-chord arrays live in memory and are discarded normally.

Source-first PV here refers exclusively to the actual C source/correspondence/execution proof and mathematical consumer. Its remaining generic compiler/runtime/OS/hardware and restricted execution-model applicability boundary is documented in [pv/README.md](pv/README.md). Kernel-only mathematics, native-assisted historical checks and external certificates are separately labeled. All selected final kernel roots permit only propext, Classical.choice and Quot.sound; no new native execution axiom or proof placeholder is accepted. Literature-backed analytic/computation statements remain explicit premises. No recipe proves optimality, a universal 0.8 obstruction, a global record, all IEANTN source claims or official Comparator approval.

## 6. Optional packaging, reports and model-runtime reconstruction

Ordinary Lake packaging has actually passed all 12 final Solution projects and their exact final type/value/axiom auditor. It is separate from the direct cold source closures. The exact 172-provider/19-group registration is `integration/LAKE_PROVIDER_MANIFEST.json`; the final phase and its separate evidence are documented in [integration/final-integration-v2/README.md](integration/final-integration-v2/README.md). The earlier `integration/HANDOFF_INTEGRATION.json` is the preserved historical ten-project handoff, not this final twelve-project receipt. With the documented study-host mappings prepared, its checked frontend is:

```sh
python3 -OO /absolute/network/Solutions/RH080Study.v1/integration/run_lake_solutions.py \
  --run /absolute/fresh/final-lake --scheduler-threads 8
```

The twelve-project theorem audit is a scoped pass, not a whole-repository check pass: the latter preserves exactly 49 inherited receipt-repository identity errors. The final integration records their unchanged ancestor comparison; it does not rewrite them or claim official Comparator/Nanoda approval. That historical comparison additionally needs the pinned Git ancestor objects.

This reads the inherited host-mapped `Solutions/RHOnePrimeEvolution.v1/scripts/LOCAL_CONTEXT.json` and expects the prescribed generic-only links/private generic copies and their receipts. It does not automatically bootstrap those clean-machine metadata mappings. The final direct-source recipes above do not need that optional packaging setup or an old application proof bank. See [integration/README.md](integration/README.md); the original ten-project receipts remain historical, distinct from the final twelve-project addition.

The report is already a standalone offline HTML with embedded licensed math fonts. Browser QA is separate from mathematical proof acceptance:

```sh
python3 -m pip install -r /absolute/network/Solutions/RH080Study.v1/reports/requirements-browser.txt
python3 /absolute/network/Solutions/RH080Study.v1/reports/check_report_browser.py \
  --html /absolute/network/Solutions/RH080Study.v1/reports/RH080_COMPLETE_REPORT_EN.html \
  --repository /absolute/network --verify-source-links \
  --browser /absolute/pinned/chromium-headless-shell \
  --output /absolute/fresh/report-browser
```

Use the pinned Playwright 1.62.0/Chromium version documented in [reports/BROWSER_QA.md](reports/BROWSER_QA.md), and repeat in normal/-O/-OO with fresh outputs. Source-link enforcement needs the report's pinned Git commit and objects; an extracted source-only ZIP without Git history cannot establish that local Git-object gate. Remote publication/delivery remains a separate release check. Rendering packages and source-paper access are not required merely to read the delivered HTML.

For **optional model-runtime reconstruction only**, restore the three large generic dependency-tree inventories omitted from the compact ZIP:

```sh
python3 -OO /absolute/network/Solutions/RH080Study.v1/release/fetch_optional_runtime_references.py \
  --repository /absolute/network \
  --receipt /absolute/fresh/optional-runtime-inventories.json
```

[release/OPTIONAL_RUNTIME_REFERENCES.json](release/OPTIONAL_RUNTIME_REFERENCES.json) pins exactly three paths, sizes and SHA256 values at immutable source commit `ee96a8c89ea40635bd4ccb0a0a1b450114ff52fd` (C3). The fetcher verifies public downloaded bytes and never overwrites a differing file. Those approximately 25MB of generic inventories are **not mathematical source inputs, numerical certificates or prerequisites for any proof route above**.

Fresh exposure/model sessions additionally require the original frozen paper corpus, native/backend account and service access, pinned runtime/packets, exact isolation setup and matched budgets. The public bundle contains identities, scripts, curated outputs and recipes, not all copyrighted papers or private reasoning traces. Repeating a model service is not a bitwise replay: hidden provider revisions and sampling seeds were not exposed. The original twenty and corrected eight outcomes remain immutable; later numerical checks, formal completion and canonical adapters remain posthoc. [exposure-runtime/README.md](exposure-runtime/README.md), [ablation/followup/README.md](ablation/followup/README.md) and the protocols explain the additional prerequisites. No model or paid service is called by the mathematical reproduction commands in this guide.

All listed frontend argument shapes were checked against the actual `--help` CLIs. The two Arb-importing helpers were checked with the recorded flint interpreter after the standard-library interpreter correctly reported the missing flint dependency. This documentation pass did not rerun the heavy experiments or turn an unexecuted combined wrapper into an accepted run.
