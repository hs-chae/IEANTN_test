# Reproducing the frozen RH study

`reproduce_study.py` runs the completed mathematical experiments from a clean repository clone or an extracted source bundle. Application proof objects from historical `/data`, workspace or development banks are not inputs. The same script works after relocating the source tree. It preserves each child runner's separate PLAN, source/object/compiler/log hashes, actual commands, resource measurements and atomic acceptance receipt. It does not rewrite the original experimental outcomes.

The default complete run performs deterministic numerical/source regeneration, the source-first C program and canonical integration, the new cube and zero-count consumers, the same-source octic cube completion, the exact Pareto cube completion, and both full cold Gaussian/Fourier/ANT closures. Each Gaussian closure rebuilds all 80 selected modules, including every cell and imported generic LeanCert source. The C source-first closure rebuilds 45 modules and then appends eight canonical/control files. Only the eight explicitly pinned generic Mathlib/package libraries are cached.

## Bootstrap the compact source archive first

A compact evidence archive omits exactly the49 large generated cell modules enumerated in `GENERATED_CELL_SOURCES.json`:25 degree80 chunks and24 degree56 chunks. It retains all generators, exact candidates, partitions, expected hashes and the278-input manifest. This is an explicit file population; no heuristic source selection is used. Original accepted sources remain in Git/local proof banks.

Before the mathematical wrapper, restore those exact missing files:

```sh
python3 -OO /absolute/network/Solutions/RH080Study.v1/materialize_generated.py \
  --repository /absolute/network \
  --scratch /absolute/fresh/scratch/cell-bootstrap
```

The bootstrap uses the existing exact-rational generator, checks each generated file against both the original cell manifests and the complete input manifest, then atomically installs only missing files. It never overwrites an existing different file and rejects missing non-generated inputs. It finishes by verifying all278 exact input hashes. Temporary raw arrays are hashed and removed after successful materialization. Source generation is not Lean proof acceptance; execute `reproduce_study.py` afterward.

The actual compact-extraction test began with all49 files absent and no application objects, restored all49 in94.55seconds, and passed the complete278-file byte guard. The actual no-overwrite and missing-input controls run under normal Python, `-O` and `-OO`. A full Git checkout already containing these files uses the same command as a no-write verification. `--check-only` reports the exact missing population without changing source; `--keep-scratch` retains the regenerable intermediate data when inspection is needed.

## Prepare generic infrastructure

Use Linux x86-64, Python 3.11, Git, GNU `time`, `prlimit`, a C11 compiler and the exact Lean binary described in `estimates/DEPENDENCY_PINS.json`: Lean 4.34.0-rc2, upstream commit `6a10ac8c22beadecabdbb0919c2b50214762f91d`, binary SHA-256 `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`. The actual accepted C compiler was GCC 11.4.0. The mathematical application replay uses Python's standard library; NumPy, SciPy, python-flint and model credentials are unnecessary for its default lane.

Install the pinned Lean toolchain with Elan, then restore the generic dependencies in the exact repository `lake-manifest.json`. Mathlib is pinned to `71a80585ee495fc24472fd0eaffc89d94e4fd8d6`; the manifest supplies every dependency's Git URL and exact revision. From the restored clone, the usual pinned setup is:

```sh
elan toolchain install leanprover/lean4:v4.34.0-rc2
lake exe cache get
```

Do not run `lake update` to advance dependency revisions. `lake exe cache get` is an infrastructure preparation step; it is not a mathematical acceptance receipt. If cache service access fails, build those same pinned generic packages from source using the pinned toolchain. No previous IEANTN application `.olean` is needed.

The checked generic library directories must be under the documented `.lake/packages/<name>/.lake/build/lib/lean` layout and their tracked Git sources must be clean. The wrapper calls the existing `prepare_proof_context.py`, then independently checks the actual compiler SHA/version, all eight package names, ordered revisions and source cleanliness. `Cli` may exist as a Lake dependency but is not one of the eight reused Lean libraries. A source archive does not contain these external Git repositories or binaries; install/restore them explicitly. Their `.git` metadata is required to check the pinned generic revisions.

## One complete command

Run outside any existing output directory. Substitute absolute paths; select the actual pinned `lean` executable, not the Elan launcher whose bytes have a different hash:

```sh
python3 -OO /absolute/network/Solutions/RH080Study.v1/reproduce_study.py \
  --repository /absolute/network \
  --compiler /absolute/toolchains/leanprover--lean4---v4.34.0-rc2/bin/lean \
  --packages /absolute/network/.lake/packages \
  --run /absolute/fresh/scratch/rh-study
```

A previously generated checked generic-context JSON can be supplied using `--context /absolute/context.json` instead of the `--compiler`/`--packages` pair. Its absolute paths refer only to explicitly installed generic infrastructure. The archived contexts record historical paths for provenance; copying such paths to another machine is not reproduction.

A source/context/CLI preflight uses the same arguments plus `--check-only`. It reconstructs actual source import closures, checks the frozen file inventory, checks tools and pins, and executes the real child help and safe PV preflight routes. Its receipt is `PREFLIGHT.json`, explicitly not a proof success. It never creates a mathematical `RESULT.json`.

The default all-lane reproduction includes all controls. `--without-controls` is available for a separately labeled proof-only rerun and records that omission as `PASS_STUDY_REPLAY_CONTROLS_OMITTED`; the full-success status is reserved for the all-lane run with controls. It must not be presented as the checked full procedure. Historical original baseline reproduction is optional with `--include-baseline`: this additionally rebuilds the 300-module predecessor packet and 53-module predecessor Gaussian packet; their original accepted results remain unchanged.

## Exact constituent routes

Every command below is issued by the wrapper with fresh output directories; none uses the historical default private paths of older frontends:

| Scope | Actual frontend and explicit inputs | Verification tier |
|---|---|---|
| C dual | `pv/reproduce_joint.py --repository R --context C --run O/pv`, then `pv/verify_joint.py --run O/pv --output O/PV_READBACK.json` | Source-first PV for the fixed scalar C program, plus its L1 Fourier mathematical consumer |
| Canonical dual nodes | `pv/reproduce_canonical.py --repository R --context C --accepted-run O/pv --run O/canonical` | Separate eight-file append against the unchanged fresh C bank |
| Cube 0.965 from exp(6) | `estimates/reproduce.py --repository R --context C --run O/cube --lane cube` | Conditional kernel mathematics; published analytic input predicates remain explicit |
| Zero-count envelope | `estimates/reproduce.py --repository R --context C --run O/zero --lane zero` | Kernel minimum/transport consuming both Bellotti–Wong clauses and BPT |
| Same-source cube 0.78146 from exp(8) | `estimates/same_source/reproduce.py --repository R --context C --run O/same_source` | Kernel completion using the unchanged original octic family |
| Pareto cube 0.9669924 from exp(8) | `estimates/pareto966/reproduce.py --repository R --context C --run O/pareto966` | Kernel completion retaining the earlier 0.965/exp(6) node |
| G80 Fourier/ANT | `primal80_gap/reproduce_joint.py --context C --lean-cert-source R/Solutions/RHOnePrimeEvolution.v1/gaussian_gap/portable/source --out O/g80 --workers 4 --worker-memory-gib 32` | Complete 80-module cold kernel proof, explicit general CMS source predicates and RH |
| G56 Fourier/ANT | Same explicit arguments to `primal56_gap/reproduce_joint.py`, output `O/g56` | Complete 80-module cold kernel proof of the original fixed degree56 input and actual consumers |

Here `R` is the supplied repository, `C` the newly checked generic context and `O` the fresh run directory. The wrapper never passes `--reuse-cold-leaves` or `--accepted-new-cell-bank`. The repository-contained seven-file LeanCert source provider is rebuilt in each Gaussian run, rather than loaded from an old object bank.

The default controls execute real C-source mutation checks and source/readback CLI guards under normal Python, `-O` and `-OO`, along with exact theorem/type/input-consumption controls for the mathematical consumers. A rejected changed claim shows that the preserved proof does not prove that altered contract; it is not a mathematical counterexample. The corresponding per-experiment READMEs describe their controls. No acceptance check is implemented using Python `assert` or `__debug__`.

## Deterministic source and data regeneration

`--lane numerics` performs all numerical/source regeneration without rerunning Lean proofs. Its result says this is not proof acceptance. It checks all ten generated sine source files; deterministically recreates all 1193 G80 cells and 1135 G56 cells, partitions and exact coefficient associations; reruns both rational Fourier transform generators in an experiment-owned shadow repository; regenerates the actual C AST/source character representation; compiles the unchanged C source and checks its actual eight output bytes. Transform generators intentionally write beside themselves, so they run only in the shadow copy. Original sources remain unchanged.

The fixed rational candidates and original timely polynomial are preserved inputs. Regenerating the certificate data from those inputs does not require rediscovering the candidates with an optimizer. There is no random seed in this deterministic replay. `REPRODUCTION_INPUTS.json` gives repository-relative exact hashes for the proof source, generators, coefficient/partition manifests, pinned inputs, compiler-context helper and generic dependency manifests needed by the completed lanes.

## Resource policy and evidence

The full wrapper sequences lanes. It preserves a 256 GiB host RAM reserve; individual Lean processes normally have 32 or 64 GiB address-space allowances. The complete C-AST execution proof runs alone at 256 GiB. The selected Gaussian runs use four workers of 32 GiB each, below the separately authorized 300 GiB experiment allowance. Historical experimental trial limits and matched conditions are unchanged. Do not infer available RAM from free disk.

The high-resource run requires the actual host capacity checked by the child frontends, including at least 1 TiB free disk for Gaussian admission. This is a capacity/admission policy, not a claim that the replay consumes 1 TiB. The observed source-first C proof peak was about 96.64 GiB RSS. Per-command GNU peaks, CPU/wall times, sampled process-tree RSS where implemented, final directory bytes and OOM/SIGKILL observations remain in the actual child receipts. Final directory size is not exact peak disk, and summed/shared process RSS is not exact physical host peak.

Preserve sources, locked inputs, accepted proofs and compact receipts. Large exact-rational arrays, shadow copies and source-generation intermediates can be regenerated. After verifying their receipts and hashes, preview and remove only the run-owned regeneration directory or disposable CLI fixtures; never delete the repository or the only accepted proof/evidence bank. The original campaign cleanup receipts remain historical evidence; this wrapper does not delete unrelated workspaces.

## Optional scopes and limits

- `--lane figure` rebuilds the exact scalar comparison theorem. It does not itself establish a new ANT reduction. To render the existing plot, run a copy of `reports/plot_population.py` in a fresh output folder with the pinned Matplotlib version in `reports/POPULATION_FIGURE.json`; SVG/PDF/CSV are illustrations of stated formulas, not prime data or numerical proof inputs.
- `--lane alternatives --flint-python /absolute/flint-env/bin/python` reproduces the bounded scalar obstruction and external Arb sensitivity probe. It requires python-flint 0.9.0. The external interval output is E evidence, not source-first PV or a new zero-sum estimate. The parameterized source argument remains written mathematics.
- `functional/reproduce_external.py --primary /fresh/extracted/pinned/original-supplement --run /fresh/external-run` requires the original paper supplement whose exact file hashes are in `functional/SOURCE_PIN.json`. It is not bundled as if present and is not silently fetched or replaced. That original program's normal-Python assertions are preserved; the separate independent checker uses explicit guards. These external runs do not replace the completed Lean/C proof chain.
- Rerunning the compact LP search requires the exact NumPy/SciPy versions declared in `functional/regenerate_compact_witness.py`. It is optional discovery reproduction; the fixed exact witness and its proofs do not depend on a new LP result.
- Controlled discovery-model sessions require the original pinned Codex/backend/runtime, model access, packets, isolation setup and budgets. Their outputs are not byte-reproducible stochastic transcripts. The preserved locked sessions and outcomes support retrospective analysis; the deterministic wrapper does not rerun them or promote posthoc formal completions into primary successes.

The remaining trust boundaries are the pinned Lean kernel/generic infrastructure, compiler/runtime/OS/hardware, the selected C execution model's adequacy for its stated scalar fragment, and the declared literature-backed mathematical predicates. Actual main/cast/format/return logic is proved, but `printf` may fail: successful output capture is explicit and conditional, not assumed as a generic platform fact. No unrestricted optimizer, universal 0.8 prime-gap obstruction, source-paper computational verification, best-known record, optimality or official Comparator approval is claimed.

After the numerical/whole-pipeline result and artifact inventory have been checked, the included bounded cleanup script verifies every selected generated file against its recorded SHA and removes only six fixed regenerable directories:

```sh
python3 Solutions/RH080Study.v1/cleanup_reproduction_scratch.py \
  --run /absolute/accepted/study-run
```

It preserves original inputs, every accepted proof/source/object bank, compact receipts and the complete generated-artifact hash inventory. Its preview plan precedes deletion. The checked reproduction run removed about1.025GB of redundant exact arrays/source shadows using this procedure.

The optional additive native replay source/template/launcher and actual NOAUTH namespace/proof-import receipts are documented in `exposure-runtime/README.md`. The clean-root fixture and the V0/V1 proof-support availability checks ran successfully with zero real model inference; research-model outputs remain nondeterministic and no new research trial is claimed by those fixtures.

## Optional ordinary Lake packaging replay

The completed direct source replays above prove the selected final consumers without historical application objects. The separate ordinary Lake integration has also passed all ten projects on the study host. Its current frontend is `integration/run_lake_solutions.py --run /fresh/out --scheduler-threads 8`; see `integration/HANDOFF_INTEGRATION.json` and `integration/PUBLIC_ALLOWLIST.json` for the exact accepted commands, 164-source provider inventory and configuration hashes.

This packaging route has additional host-mapping prerequisites and is **not automatically bootstrapped by the mathematical wrapper**. It reads `Solutions/RHOnePrimeEvolution.v1/scripts/LOCAL_CONTEXT.json` for compiler and nine generic package identities/host paths. A clean machine must generate matching host-mapped metadata, install owned private generic copies with the required `COPY_RECEIPT.json`, and establish the prescribed generic-only links in the root, all ten Solution projects and the study. It never needs an old application `.olean` bank. The full 164-provider union in `integration/LAKE_PROVIDER_MANIFEST.json` must be present; `REPRODUCTION_INPUTS.json` describes the direct mathematical replay, not this larger packaging universe.

The actual host invocation used a delegated systemd user scope with `MemoryMax=300G`, `MemorySwapMax=0`, `CPUQuota=1600%` and sixteen assigned CPUs, then `python3 -OO .../integration/run_lake_solutions.py`. The runner requires at least1TiB initially available RAM, a256GiB host reserve, and16–32 assigned CPUs. The accepted primary ten-project run took1114.50seconds; a later cached ten-project rerun took17.78seconds, and30 optimization-mode controls passed. Those are real completed host builds, not a claim that the remaining clean-machine Lake metadata preparation has been automated. Direct deterministic mathematical/source reproduction remains independent of that optional packaging setup.
