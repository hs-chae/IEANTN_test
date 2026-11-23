# RHLimit source and evidence package

This is the selected source package for the new RHLimit study, preserving the
original experimental outcomes and mathematical trust boundaries. It includes
all new study sources and compact evidence, the reviewed canonical file changes,
and exact selected baseline prerequisites. It is not a copy of unrelated private
workspaces or a claim that every open analytic input has been proved.

The package contains the frozen 261-module π source graph, its 55-module spectral
extension, the source-linked box moment/PNT route, the finite absolute octic
bridge, all four closed octic contracts and final count consumers, and the final
canonical consumers specified in ROOT_FINAL_READY.json. Read the offline study
reports under network/Solutions/RHLimit.v1 for mathematical statements and limits.

## Download and restore

Place every RH_LIMIT_SOURCE.partNNN file, PARTS_MANIFEST.json and join_bundle.py
in one directory. Every part is at most 6 MiB. The helper checks its own identity,
every part hash and size, exact part membership, and the complete archive hash:

```
python3 join_bundle.py --parts-dir . --check
python3 join_bundle.py --parts-dir . --out RH_LIMIT_SOURCE.tar.gz
```

The extraction helper is supplied separately beside the parts. It checks every
member name/type and the complete file/hash inventory before accepting the tree:

```
python3 archive_tools.py extract --archive RH_LIMIT_SOURCE.tar.gz --out restored
python3 restored/prepare_bundle.py verify --tree restored
```

A rejected or incomplete restore is not verified evidence. Use a fresh output
directory. The archive has no Git metadata, application/checker proof-object
cache, owner prompt, memory, transcript, or downloaded research-paper PDF.
Source file hashes and exact baseline origins are in SOURCE_PLAN.json; the whole
archive inventory is BUNDLE_MANIFEST.json. These identities are separate from
mathematical verification receipts. Restoring an archive does not prove a theorem.

## Clean generic dependencies

Required system tools: Python 3.11+, git, GCC with GNU __uint128_t support,
GNU /usr/bin/time, and the exact Lean 4.34.0-rc2 compiler with its bundled leantar.
Install the exact toolchain using `elan toolchain install leanprover/lean4:v4.34.0-rc2`
if it is not already available. The compiler SHA256 is recorded in
GENERIC_DEPENDENCY_PINS.json and the reference
network/Solutions/RHContinuation.v1/scripts/GENERIC_CONTEXT.json. Generic package
URLs, revisions and names are pinned in the same metadata and lake-manifest.json.
Fetch all nine exact source revisions into a fresh directory:

```
python3 restored/FETCH_GENERIC_SOURCES.py --out /absolute/packages
```

That command uses only the pinned URLs and commits and leaves existing directories
untouched. To validate existing checkouts without writes or downloads, add
`--check`. Do not run an unpinned lake update.

The reused, previously checked generic bootstrap downloads exact official cache
archives, builds 38 missing generic tooling modules from included pinned source,
and runs the unchanged full legacy inventory gate:

```
python3 restored/BOOTSTRAP_GENERIC.py \
  --packages /absolute/packages --compiler /absolute/toolchain/bin/lean \
  --out /absolute/scratch/generic
```

Use the generic_context path printed in that successful receipt for the next
step. The bootstrap requires network access for the pinned official cache URLs.
The included generic metadata transport contains historical bookkeeping and one
explicitly documented IDE reference-usage metadata exception needed by the
unchanged old inventory validator. It contains no application proof objects;
semantic generic objects are downloaded or compiled, then checked against exact
inventories. The corresponding exception and trust boundary remain documented
in generic-transport/METADATA_MANIFEST.json.

An existing generic context may be supplied instead only if the compiler,
package commits and source cleanliness pass the same pinned checks. No old
application or LeanCert object directory is accepted as a substitute for fresh
application/checker compilation.

## Reproduce the mathematics and numerical execution

All scratch output must be fresh and outside the restored package. First check
package/source/dependency inputs, then run the bounded dependency-aware pipeline:

```
python3 restored/REPRODUCE_RH_LIMIT.py --context /path/to/GENERIC_CONTEXT.json \
  --out /absolute/scratch/preflight --check
python3 restored/REPRODUCE_RH_LIMIT.py --context /path/to/GENERIC_CONTEXT.json \
  --out /absolute/scratch/verification
```

The preflight explicitly labels the spectral and canonical routes as pending
until their fresh application foundations exist. The full command rebuilds
those foundations before invoking them; it checks every child status and the
final canonical receipt. A failed route retains its logs and partial result
without issuing final acceptance. The C-log route recompiles and runs the exact
verified_finite_log.c on all 127 required inputs, regenerates numerical data,
checks controls in normal Python/-O/-OO, and recompiles the connected Lean proofs.
The other numerical bounds retain their documented kernel-only classification.
No random seeds are used.

For measured process-tree RAM and a durable exit receipt, wrap the full command
with `run_replay_bounded.py --record /absolute/scratch/resources --limit-gib 80
--group-gib 240 --wall-seconds 10800 --` followed by the same Python command.
The process limit and aggregate group limit are separate. The wrapper records
actual sampled process-tree RSS, wall time, host RAM and initial free disk, and
stops only its owned process group if a configured limit is exceeded.

The original source controllers preserve their resource policies: up to 48 or
80 GiB virtual address space per Lean process, eight Lean threads where specified,
and a 512 GiB host reserve where the historical source controller requires it.
Use a machine satisfying those actual admission checks. Available RAM and disk
are separate requirements. The default wrapper runs at most three independent proof routes at once. It
admits a group of at most 240 GiB only when at least 752 GiB is available,
preserving 512 GiB for the host. The spectral extension starts only after the
π source replay passes. Canonical consumers start only after all five components
pass. Aggregate logs and acceptance receipts are written only on the main thread.
If one component fails, no further components start; already running components
finish and their evidence is preserved. Add `--serial` to run one route at a time;
the same host-admission guard remains in force.
Expect substantial CPU time and generic-download/storage use; consult the study
receipts for measured peak RAM, disk use and execution times. No obsolete 4 GiB
limit is introduced.

Source-first PV means actual C source → AST → execution semantics → mathematical
correctness → the actual theorem consumer. Ordinary Lean interval/rational
proofs, kernel-only checks, native-assisted evaluation and certificate checking
are not renamed PV. The reports identify reused C components and remaining
compiler/runtime/ABI/OS/hardware trust assumptions. RH, literature inputs and
unproved analytic contracts remain explicit, including the octic explicit
formula and whole zero-sum estimate. Neither .076 nor the 610-billion milestone
is promoted by a successful archive restore.

After a checked run, generated numerical outputs and temporary scratch can be
regenerated deterministically. Keep source, parameters, dependency identities,
concise results, hashes and verification receipts. Preview any cleanup and delete
only verified regenerable files owned by that run; preserve accepted proof
artifacts and original evidence. Never clean an unrelated checkout or generic
cache as a side effect of reproduction.
