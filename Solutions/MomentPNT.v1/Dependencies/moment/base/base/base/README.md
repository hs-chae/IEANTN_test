# Complete source main, observed final bytes and the conditional PNT

**Prepared source/evidence input; the complete 3,942-source replay has not yet
finished.** This component preserves all original C, algorithms, numerical
parameters, theorem statements and analytic assumptions. It never changes
historical experimental outcomes or promotes a numerical observation as a
mathematical premise.

The final selected root is
`SynergyHeightC.MainObservedProgram.complete_source_main_observed_and_pnt`.
It composes source-bound static globals evaluated from empty application memory,
the actual 768-row C loop with actual running totals, source point/edge/budget
calculations, the physical final total read, the same interval's emitted 128
bytes, checked modeled flush, normal return and the conditional ANT theorem:

**Eπ(x) ≤ 0.008441646 · x⁻¹⁄⁸ for x ≥ exp(330).**

All eight original PrimaryInputs fields and six analytic hypotheses remain
explicit. The source program uses a defined successful-stdio **model scenario**.
It does not assert that arbitrary real host writes succeed. A separate pinned
actual C compile/run produced 98,432 bytes; its final 128 bytes are formally
compared with the independently source-proved final interval. Observations do
not replace the source computation. Kernel-only byte comparisons and raw host
execution are not source-first PV by themselves; the actual source/AST/execution,
arithmetic correctness and ANT consumption chain is the required connection.

## Contents and exact populations

The unchanged nested base contains 1,412 source modules and 2,350 selected roots,
then the corrected source-only 860-module frame/weight append with 3,263 roots.
This complete-main extension adds **1,670 modules and 6,363 roots**. The union
contains **3,942 distinct application modules and 11,976 selected roots**.

The extension includes all 768 actual source input-edge constructions, all 768
actual source budget suffixes and recurrence proofs, their aggregators, complete
main/stdio source composition, source-computed global entry, concrete modeled
I/O trace, fresh observed-byte comparison and final ANT consumer. Application
objects are never distributed or loaded from developer banks.

`SOURCE_LOCK.json` pins the exact mathematical/executable sources separately
from `REPRODUCER_LOCK.json`. Original observed evidence and its warm proof
receipts are retained under `evidence/`. They are provenance; they do not imply
that this larger clean replay or final namespace isolation has passed.

## Clean public environment

Use Linux x86-64, Python 3.11 or later, Git, `/usr/bin/time`, the exact pinned
Lean 4.34.0-rc2 distribution and the exact public mathlib/package commits from
the locks. Prepare their public generic caches, then record the environment:

```sh
python3 -OO base/base/prepare_environment.py \
  --toolchain /absolute/path/to/lean-4.34.0-rc2-linux \
  --mathlib /absolute/path/to/pinned/mathlib \
  --out /absolute/path/outside-this-capsule/environment.json
```

No previous research application objects or original repository checkout are
required. The generic compiler/runtime/library caches remain disclosed trust
inputs, with source commits and compiler/core identities checked by the recipe.
The C build uses the recorded GNU C++11/Boost/header and Linux ABI contracts;
this component does not verify the generic compiler or library implementation.

## Full chained reproduction

Reserve resources against actual available RAM independently of free disk.
The study allows up to 300 GiB aggregate RAM and 300 GiB scratch after checking
the independent 1 TiB availability conditions, while preserving host reserves.
An externally enforced scope of up to 256 GiB/16 CPUs is suitable for the
current staged plan. The obsolete 4 GiB limit is not used. Source proof jobs
are explicit; heavy frame/weight and edge/budget groups run in separate phases.

```sh
python3 -OO reproduce_all.py \
  --environment /absolute/path/environment.json \
  --out /absolute/path/fresh-complete-run \
  --base-jobs 8 --prior-jobs 14 --frame-jobs 14 --weight-jobs 6 \
  --jobs 14 --edge-jobs 14 --cell-jobs 12
```

This regenerates actual C/numerical data and compiles the unchanged 1,412-module
base, then compiles the 860-module frame/weight append, then rebuilds the 1,670
new complete-main modules. Before each stage, every reused application object
is associated with that same pipeline's complete fresh source proof receipt,
source hash, command, object hash, log hashes and complete standard-axiom audit.
Each new stage seeds a **single coherent object bank**, verifies all copied
hashes and excludes every old warm application bank. This avoids the original
V1 two-bank Lean namespace import failure; the corrected V2 base is preserved.

The complete-main stage compiles/runs the pinned C program again, recreates the
exact observation Lean source from its fresh physical bytes, requires a byte
identity with the locked observation source, and only then compiles the source
proofs and audits all 11,976 root closures. Successful receipts are atomic and
written only after the entire pipeline passes. Python `-O`/`-OO` disables no
acceptance condition.

To continue from an already completed identical fresh 2,272-source run, use:

```sh
python3 -OO reproduce.py \
  --environment /absolute/path/environment.json \
  --prior-run /absolute/path/completed-2272-run \
  --out /absolute/path/fresh-complete-main-extension \
  --jobs 14 --edge-jobs 14 --cell-jobs 12
```

`--prior-run` may be the complete chained base run or its accepted append run.
The original 1,412-source run referenced by its association receipt must also
remain available. Every source/object/log/validator/audit association is checked
again; a partial or mismatched prior run is rejected. Checkpoints are preserved
as partial work and never count as proof acceptance.

## Controls and observation regeneration

```sh
python3 -OO check_controls.py \
  --environment /absolute/path/environment.json \
  --out /absolute/path/fresh-controls
```

The controls exercise the actual CLIs in normal, `-O` and `-OO` Python modes,
including source-only identity checks, invalid parameters, missing prior
acceptance, source corruption and proof-admission/native diagnostics. They also
compile and run the actual C program and recreate the observation source in
each mode. A controls-only receipt is not a mathematical proof receipt.

`regenerate_observation.py` adapts the original observation generator only for
portable, fresh output paths and the unchanged nested C source tree. The original
generator is retained under `provenance/`. Its numerical parsing and generated
Lean text are unchanged. The original 98,432-byte observation and 128-byte tail
are small retained evidence; fresh reproduction must regenerate and match the
actual C output rather than using these files as numerical providers.

## Results, trust and cleanup

The final receipt records every execution command, compile result, source/object
and output/log hash, elapsed time, final consumer and complete axiom closure.
Resource scopes separately record RAM samples/available peaks, individual
compiler RSS, elapsed time, disk measurements and OOM events. Sampled peaks are
lower bounds when true peak counters are unavailable; unmeasured peaks are
reported as such. Actual runs and unresolved mathematical obligations must be
distinguished from resource or import failures.

After completed reproduction is checked, remove only verified experiment-owned
regenerable binaries, copied negative fixtures, redundant temporary arrays and
caches, retaining cleanup previews/receipts. Preserve locked sources, accepted
proof artifacts, original research evidence, hashes, verification receipts and
the minimal observed bytes. The recipe never deletes unrelated workspaces.

This is a complete selected source-program graph input. Host source-cold replay,
final namespace-isolated acceptance, the original 68-function Scoped Winner
migration, and the wider controlled exposure research project are distinct
completion claims. None is implied merely by extracting this archive.
