# Reproducing the frozen PNT+ and IEANTN baselines

The baseline proof replay passed. It rebuilt 36 native PNT+ modules (35 original
modules and the generated import root), 150 historical IEANTN core modules, and
the four unchanged Dudek–Platt proof modules in separate solution contexts. The
ten selected PNT+ theorems and both selected Dudek–Platt theorems have only
`propext`, `Classical.choice`, and `Quot.sound` in their inspected axiom closures.
No model was called and no experimental score was changed.

Both the checked-cache component replay and the complete public-source cold
bootstrap have passed. The cold run used no preexisting host toolchain, generic
source/object or application proof cache. It fetched both exact official Lean
releases, both project sources, all 22 pinned dependency sources and the required
official generic binary caches. All 520 resulting proof artifacts have identical
SHA256 hashes in the warm and cold runs.

The cold bootstrap completed through two preserved technical routing repairs and
validated checkpoints in the same originally empty output directory. It is not
claimed that the final corrected script was separately rerun uninterrupted from
an empty directory. The compiler and all of Mathlib were not built from source;
official pinned release/cache distributions remain trusted. Baseline replay does
not replay model sessions or validate later mathematical candidates.

## Files to preserve together

The portable entrypoint is `scripts/reproduce_baselines.py`. It requires only
`scripts/baseline_reproduction_pins.json.gz` beside it, ordinary system tools,
and access to the pinned public download endpoints. The compressed manifest
contains exact project source inventories, dependency commits and source hashes,
toolchain release digests and file inventories, and hashes for the optional
generic binary caches. It contains no model credential or model transcript.

`scripts/BASELINE_DEPENDENCY_PINS.json` is the small readable version/pin index.
`scripts/BASELINE_REPRODUCTION_COMMANDS.json` preserves the exact executed
component commands and the distinct proposed public-source bootstrap command.
Licenses present in the pinned projects and dependencies are retained with the
regenerated source trees.

The accepted component run used the preserved source
`reports/baseline_reproduction_engine_v1.py`, SHA256
`5eafee98e8fddd11a4a1ce76a4e3b17ea342860677f9588699c0c4f7e0af2a9c`.
The public entrypoint subsequently gained early complete-cache/output-directory
checks, a script-immutability guard, and accurate selected-arm receipt text.
The v2 build/audit functions were byte-identical to those executed in v1, as
recorded in `BASELINE_REPRODUCTION_V2_DELTA.json`. The later cold bootstrap exposed
and repaired two actual dependency-routing gaps. Its final executed script is
SHA256 `3f6715744151cfbf46354c648a3a192250acfc17addbfba92da316af366bb13e`;
the current compressed pin manifest is SHA256
`de395902e63692e37c7e043f8c2799b3ea84e3a8929aed21048ea12adf336555`.
Earlier source and pin versions, failed traces, and successful owned checkpoints
remain preserved; no mathematical source file or dependency commit changed.

## Source versions and allowed projections

| Environment | Original source commit | Compiler | Mathlib |
|---|---|---|---|
| Native PNT+ | `AlexKontorovich/PrimeNumberTheoremAnd@a4fb6989b07e9c76b511807ae93e33e25b820e9b`, 2026-11-15 | Lean 4.35.0 | `56a005855ea17e0b0958f73ec801ae140b0a1679` |
| Historical IEANTN | `teorth/IEANTN@ef21db9ba5dceffd976da71e24f8497b3a13f798`, 2026-10-31 | Lean 4.34.0-rc2 | `71a80585ee495fc24472fd0eaffc89d94e4fd8d6` |

The IEANTN cut precedes the local QRH experiment modifications; it is not claimed
to predate publication of the QRH result. All 710 original historical files are
retained. Native PNT+ retains exactly its original native import closure and
excludes the legacy IEANTN subtree and any native module depending on that
subtree. It is not a translation or flattening of IEANTN. Only the native import
root is generated; retained mathematical source files are unchanged.

No Git checkout or original research workspace is required by the portable
entrypoint. Project source archives are downloaded from the immutable public
commits, and every retained source file is checked against its frozen hash.
Generic dependencies are either downloaded at their exact commits or copied
from a complete cache map after whole-tree hash validation.

The archives and administrative logs in a reproduction output directory are
trusted-coordinator material. Do not mount the whole output directory into a
controlled worker: a whole upstream PNT+ archive also contains its excluded
legacy IEANTN subtree. Worker runtimes use only their separately audited, sealed
source/object leaves and their own packet manifests.

## Clean-environment bootstrap command

Use Linux x86-64, Python 3.10 or later, a functioning user systemd manager,
GNU `time`, `cp`, `taskset`, `tar`, and `zstd`, and the normal Linux runtime/C
toolchain needed by the pinned Lean releases. Public GitHub downloads and the
official Mathlib cache endpoint must be reachable. The output directory must
not already exist; its parent must be writable and already exist.

From the extracted study bundle:

```sh
python3 -I -B scripts/reproduce_baselines.py \
  --out /absolute/writable/parent/fresh-baseline-replay \
  --memory-gib 32 --scratch-gib 48 --cpus 0-7
```

Choose eight or fewer CPUs within the machine's allowed affinity. If `--cpus` is
omitted, the script chooses the first eight available CPUs. `--arms PNT` or
`--arms IEANTN` restricts the replay. The script checks separate RAM and disk
headroom before launching. It uses a private output tree, copies/downloads its
own toolchains and generic dependencies, and never writes to an original
checkout or an optional reused cache tree.

The scope requests 32 GiB RAM by default; 64 GiB is an explicit supported choice.
Swap is disabled for the scope, the descriptor allowance is 65,536, and actual
CPU affinity is limited by `taskset`. The program reads back the memory/swap
limits and CPU affinity before accepting the run. An absent effective CPU quota
file is not presented as an enforced quota. `PATH` and `LEAN_SYSROOT` select the
correct compiler independently for each arm. All writable HOME, temporary,
download and cache directories belong to this replay.

Without a cache map, the script downloads the official Lean release archive,
checks its recorded archive digest and retained file hashes, downloads the
pinned dependency sources, and fetches only the Mathlib cache closure required
by the frozen module import inventories. It builds the original Architect
library where required, then compiles the application source graphs. It does
not ask Mathlib to rebuild every unused source module. Directly imported generic
modules absent from that narrowed cache are built from their exact pinned source.
This cold route has now completed in `reproduction-cold-v1/`, using the preserved
owned-checkpoint recovery described below.

## The executed cold bootstrap and checkpoint recovery

The cold output was initially empty. No cache map was supplied. Its two exact
Lean release archives total 1,174,762,504 bytes; their digests and all retained
compiler-distribution file hashes were checked. Twenty-four source archives
(two projects and 22 generic dependency versions) were downloaded at immutable
commits. Together the 26 preserved archives total 1,254,095,979 bytes.

The initial invocation exposed a metadata classification error: the prepared
ProofWidgets source cache had retained `widget/package-lock.json.hash`, which is
not an original repository source file. The original `package-lock.json` is
present and hash-pinned. The corrected recipe uses the freshly downloaded pinned
`Lake.computeFileHash`/`Lake.writeFileHash` implementation to regenerate the exact
16-byte checksum; it does not hardcode a numerical output. The source of this
behavior is the pinned ProofWidgets `widgetPackageLock` target and pinned
`Lake.Build.Common.writeFileHash`. `COLD_GENERATED_METADATA_REPAIR.json` records
this correction without changing mathematical source, commits or sealed runtimes.

The next invocation fetched the 3,828-file narrowed PNT+ Mathlib cache and built
Architect, then found that the directly imported `Batteries.Tactic.Lemma` module
was outside that narrowed cache closure. The corrected bootstrap builds that
specific generic module from its unchanged pinned source. Fourteen already
successful application source compilations were checked against their command,
source, compiler and artifact hashes and retained. Only the two failed native
compilations and pending modules continued. Failed commands and their actual
error messages remain in the evidence; they are not retroactive successes.

An interrupted **owned cold run**, with the same source commits and no external
cache map, can be continued explicitly:

```sh
python3 -I -B scripts/reproduce_baselines.py \
  --out /absolute/writable/parent/that-incomplete-cold-output \
  --resume-cold --memory-gib 32 --scratch-gib 48 --cpus 0-7
```

Completed runs are never overwritten. Original invocations, stdout/stderr and
resource samples remain intact, while each resumed scope has fresh evidence.
A resume cannot substitute a host compiler, generic library or application
cache. It revalidates only artifacts already created in that originally empty
cold run. The final accepted cold result is
`reproduction-cold-v1/RESULT.json`, SHA256
`d2e449d6c0b4dcd7a56b6efc3ad6ebd681ab41eabc5734d6790c06df8ec68422`.

| Cold-bootstrap measurement | Observed result |
|---|---|
| Source application builds | PNT+ 35 plus root; IEANTN core 150; selected DP 4 |
| Selected theorem closures | All 12 use only standard three axioms |
| Recorded proof/bootstrap commands | 200, including two preserved failed import attempts |
| Preserved technical execution attempts | 3 |
| Sum of recorded active execution | 376.73 seconds; excludes time spent repairing the script |
| Largest observed charged memory | 8,978,255,872 bytes, lower bound on peak |
| Exact simultaneous peak | Unavailable: `memory.peak` absent |
| Largest GNU-time child RSS | 4,370,920 KiB |
| Final owned allocated-block sum | 15,600,873,472 bytes |
| Enforced owned scratch guard | 48 GiB; no stop triggered |
| OOM / OOM-kill observations | Zero in every recorded attempt |
| Accepted artifacts | 520, 67,026,722 bytes; all hash-identical to component replay |
| Model calls / score changes | Zero / none |

`BASELINE_COLD_REPLAY_READBACK.json` preserves all archive identities, command and
artifact readback, measurements and limitations. The scratch and RAM samples are
lower bounds on their peaks; disk block accounting is not an exclusive host
increment measurement. The 32 GiB memory, zero swap, CPUs 80–87 and 65,536 file
descriptor policy was read back in every actual scope. This is a cold software
bootstrap using official binary dependencies, not a full-source platform build
or source-first PV.

The tested recovery covers the bootstrap and hash-checkpointed native/core
module graphs in this recorded history. Automatic recovery of an arbitrarily
interrupted, partially created selected `Solution` directory is not implemented.
Also, a future generic-bootstrap success with a `-resumeN` command label may need
explicit journal readback rather than relying on the compact bootstrap marker.
Neither limit occurred in the completed cold history; the full command journal
and independent readback remain authoritative. These are recovery-interface
limits, not unresolved baseline mathematical proofs. A fresh output directory
remains the normal reproduction entrypoint.

These commands regenerate the consumed baseline proof closures. They do not
claim to regenerate every unused optional generic object exposed in a discovery
runtime, rerun model sessions, or reproduce future candidate computations. Exact
runtime manifests and the candidate-specific replay hooks are separate evidence.

## The executed component command

The actual run used a complete, read-only cache map containing only pinned
toolchains and generic source/object trees:

```sh
python3 -I -B scripts/reproduce_baselines.py \
  --out /absolute/study/reproduction-component-v1 \
  --cache-map /absolute/study/coordinator/BASELINE_COMPONENT_CACHE_MAP.json \
  --cpus 80-87 --memory-gib 32
```

The exact machine command is preserved in
`reproduction-component-v1/REPRODUCTION_INVOCATION.json`. That cache-map path is
a record of the tested machine, not a required path on another machine. A cache
map must provide the compiler and every declared generic source/object provider
for the selected arm. Partial maps are rejected before creating the output;
omit the option to use the separate public-source bootstrap route. The source
providers must be the exact source-only trees; an arbitrary previous build
directory containing extra files will not match the frozen inventory.

The component replay did not copy its own PNT+ proofs, IEANTN core proofs or
Dudek–Platt proofs from a cache. Those application proofs were freshly compiled.
Only generic dependency objects and compiler distributions were reused.

DPv3 and DPv2 both use a module named `Solution`. They are compiled and audited
in distinct object/search-path contexts. They must not be combined into one
search path and presented as two simultaneously imported `Solution` modules.

## Results and measurements

| Recorded measurement | Actual component result |
|---|---|
| Fresh native PNT+ source modules | 35 plus generated root |
| Fresh historical IEANTN core modules | 150 |
| Fresh selected Dudek–Platt source modules | 4, in two contexts |
| Selected theorem axiom audits | 12, all standard three axioms |
| Executed proof/audit commands | 193, all successful |
| Generated proof artifacts checked again | 520, 67,026,722 bytes |
| Replay wall time | 334.12 seconds |
| Largest observed charged memory | 18,500,128,768 bytes; lower bound on peak |
| Exact charged-memory peak | Unavailable: kernel has no `memory.peak` file |
| Largest GNU-time child RSS | 4,370,096 KiB; not simultaneous whole-scope RAM |
| Recorded OOM / OOM-kill counters | 0 / 0 at the final scope observation |
| Owned allocated-block sum | 16,320,812 KiB; can include shared reflink extents |
| Model calls / score changes | 0 / none |

The disk number is an allocated-block sum from `du`, not the exclusive
incremental physical space consumed on a concurrently used host. Source,
toolchain and object caches remain present; no cleanup was performed while
experiments could still depend on the sealed inputs.

`BASELINE_COMPONENT_REPLAY_READBACK.json` records independent readback of all
193 command evidence sets and all 520 generated proof artifacts. Per-command
arguments, stdout/stderr hashes, GNU-time logs and generated artifact hashes
remain under `reproduction-component-v1/`. Component acceptance and resource
measurements do not revise historical experimental outcomes or establish a new
tertiary improvement.

## Validation, scope and trust

The historical public v2 CLI passed 18 cases. The final cold-executed script
passed 24 actual cases across ordinary Python, `-O` and `-OO`:
original pin acceptance, corrupt-pin rejection, incomplete-cache rejection,
reused-cache/output overlap rejection, existing-output preservation, and
duplicate-arm rejection, completed-cold-output preservation, and mismatched
resume-source rejection. Rejected cases reached their exact intended error and
created no output directory. Acceptance code uses explicit checks, not `assert`.
Independent peer-review records identify the tested code versions and
confirm that no application proof-cache substitution or `Solution` context
collapse occurred.

This is ordinary Lean/kernel baseline proof checking with source identities and
reproducible build commands. It is not source-first program verification. The
pinned compiler/kernel, generic library/cache distributions, OS/runtime and
hardware remain trusted. Unused upstream native helpers can still contain
admissions; inspecting twelve selected theorem closures does not make the
entire environment admission-free. IEANTN core compilation also does not prove
every node or turn permanent `Challenge` sorries into accepted proofs.

DPv3 supplies a generic criterion implication. DPv2 still requires that
criterion and its prime-counting numerical hypothesis as premises. The replay
supplies no numerical premise as a fact. Mathematical inputs, statements,
parameters and historical source are unchanged.

No model session is rerun by these commands. Replay of locked future candidate
submissions and their mathematical/numerical obligations belongs to the separate
final-candidate reproduction pipeline.
