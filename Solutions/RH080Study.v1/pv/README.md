# Compact Fourier-dual C program and source-first verification

The completed fixed-input chain connects physical `dual_grid.c` bytes to an independently specified C grammar, a manually specified checked unsigned execution model, actual complete C-AST execution, true real trigonometric error bounds, the continuous Fourier-dual kernel, and canonical IEANTN mathematical consumers. All selected theorem closures use only `propext`, `Classical.choice` and `Quot.sound`; no native execution axiom or `sorry` is accepted.

The program computes every one of 257 grid caps from the twenty rational witness heights in `PARAMETERS.json`, including nine-term fixed-point sine calculations, and takes their maximum. It is not given the maximum as a certificate. The actual compiled output is the eight bytes `1221161\n`, at scale one million. Its full source execution is proved for these fixed inputs; this is not an unbounded global optimizer or a verified general C compiler.

The resulting mathematical statement is an actual integrable dual witness at penalty `36/11`, with its true cosine integral bounded by `123/100` on the entire real line. This gives a ratio floor `100/123` and excludes `4/5` **within the explicitly stated L1 Fourier fragment**, where both the function and its genuine Fourier transform are integrable and the objective denominator is positive. It is not a prime-gap lower bound, a global optimizer claim, or an improvement over the paper's stronger numerical dual barrier. V0 receives the identical mathematical input and certificate information: source-first PV adds verified execution coverage, not a better constant by itself.

## Accepted evidence

`HANDOFF.json` identifies exact accepted runs and metrics. Public receipts are in `receipts/`:

- `fresh-joint-v2-j2`: all 45 application sources compiled afresh with only the eight pinned generic libraries; complete C-AST execution, source syntax, main/output, sine, Fourier/continuum and final mathematical consumer; 13-root/11-edge axiom/value audit. Elapsed 935.13 seconds, summed CPU 973.48 seconds, peak individual RSS 101335824 KiB (96.64 GiB), zero SIGKILL events. Final allocated run storage was 42131456 bytes; peak disk was not separately sampled.
- `canonical-append-v1`: eight additional source files compiled against the unchanged accepted 45-module bank, including separate canonical Solution wrappers and boundary controls; seven audited roots, three closed canonical source paths, eighteen required transitive source/main/execution dependencies. Elapsed 23.19 seconds. This is a separate later phase, not retroactive initial replay coverage.
- `joint-cli-controls-v2`: 51 actual source/readback/preflight/rejection routes across Python normal, `-O` and `-OO`. The heavy kernel computation is performed once, not silently repeated by those CLI tests.
- `SOURCE_MUTATION_MODES.json`: 30 actual kernel source-check controls across all three Python modes, with two accepted harmless variants and eight rejected source mutations per mode. Finite mutation tests supplement the general proved checker-soundness theorem.

Historical failed development attempts are retained and explained in `DEVELOPMENT_NOTES.md`. Address-space allocation failures, intentional termination and a host thread-creation failure are distinguished from host OOM kills and mathematical failures. No primary historical outcome has been rewritten.

## Clean reproduction

Requirements: Linux with Python 3, Git, GNU `time`, `prlimit`, a C11 compiler, Lean `4.34.0-rc2`, and the exact eight generic package Git commits listed in `../baseline/GENERIC_CONTEXT.json` and the repository's pinned `lake-manifest.json`. Restore/build those generic library objects using the usual pinned Lean/Lake setup (`lake exe cache get` may restore generic Mathlib caches). Do not copy any predecessor application objects. The manifest supplies repository URLs and exact revisions. The library directories must end in `.lake/build/lib/lean` inside the matching `.lake/packages/<name>` Git checkouts, with clean tracked sources.

Create a local JSON context containing `compiler`, its `compiler_sha256`, and `generic_lean_path` (the colon-separated eight absolute generic library paths). The archived baseline context shows the exact schema and historical host paths; replace paths for the clean machine and hash the actual pinned compiler. The frontend checks compiler version/bytes, every exact generic Git revision, clean source and the absence of application fallback. On another platform the pinned Lean executable hash may differ; record that distinct infrastructure boundary explicitly.

Run from the repository root, substituting absolute paths and unused output directories:

```sh
python3 Solutions/RH080Study.v1/pv/reproduce_joint.py \
  --repository /absolute/path/network \
  --context /absolute/path/generic_context.json \
  --run /absolute/fresh/path/source_first_joint

python3 Solutions/RH080Study.v1/pv/verify_joint.py \
  --run /absolute/fresh/path/source_first_joint \
  --output /absolute/fresh/path/readback.json

python3 Solutions/RH080Study.v1/pv/reproduce_canonical.py \
  --repository /absolute/path/network \
  --context /absolute/path/generic_context.json \
  --accepted-run /absolute/fresh/path/source_first_joint \
  --run /absolute/fresh/path/canonical_append

python3 Solutions/RH080Study.v1/pv/test_joint_cli.py \
  --repository /absolute/path/network \
  --context /absolute/path/generic_context.json \
  --accepted-run /absolute/fresh/path/source_first_joint \
  --run /absolute/fresh/path/cli_controls
```

For source-mutation controls, run `test_source_mutations.py --help`; use the accepted fresh source/object bank as the explicit context provider, and run the actual script under normal Python, `python3 -O` and `python3 -OO`, each with a new output directory. Its command schema and exact accepted historical commands are in `receipts/source-controls/`. This is finite checker testing, not a replacement for the general grammar proof.

`reproduce_joint.py --check-only` validates only the source closure and generic pins. The full run snapshots all selected source, regenerates `DualAST.lean` and `DualSource.lean` byte for byte from the physical unchanged C file, checks every ASCII byte against the formal character list, compiles every selected proof into a fresh object bank, audits actual proof values and axioms, compiles the actual C source, executes its binary, and compares actual captured bytes with the kernel-proved serializer. Accepted receipts contain exact source/object/binary/compiler/log hashes and commands. Scripts regenerate numerical data deterministically; no random seed is used.

Normal Lean processes use two threads and a 64 GiB address-space cap. The complete C-AST execution proof is serialized alone with a 256 GiB cap and a 256 GiB host RAM reserve. These are admission limits, not measured consumption; reproduction intentionally refuses to consume the host reserve. The owner permitted up to 300 GiB per run when at least 1 TiB RAM was genuinely available. Disk capacity is checked separately. Reusing generic library objects and compiler/runtime/OS/hardware correctness remain explicit infrastructure boundaries.

Read `TRUST_AND_SCOPE.md` for the selected C semantic adequacy boundary. In particular, actual main call/cast/format/return behavior is proved, but `printf` can fail. Exact output is conditional on an actual successful performed I/O capture; success and correct output are never assumed as generic platform facts. The pure numerical C execution theorem is independent of I/O success, and the recorded physical execution separately captures the actual eight bytes.

The canonical append compiles the Mathlib-only vocabulary and node Conclusions before the source-backed implementation, audits that supplied witness/floor inputs are consumed, and closes actual node results through the complete joint source package. The final C-derived cap uses `source_result_controls_grid` and `actual_numerical_execution`; a transitive audit rejects the ordinary kernel-only `Model.sampleBound_all` shortcut.

Experiment-owned disposable CLI fixtures may be removed only after the retained result/log/hash evidence and deterministic regeneration commands are checked. `CLEANUP.json` records the exact approved targets. Original source, accepted proof banks and all unique research evidence are retained.
