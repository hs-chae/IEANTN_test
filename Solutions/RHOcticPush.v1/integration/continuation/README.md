# Reproduce the octic, Box, signed-spectral and PNT-feedback results

The public packet contains the exact source closure, C include resources, frozen
mathematical statements and pinned proof controllers. It excludes application
object caches, the broad historical work snapshots, private context and primary
PDFs. The base proof set has723 module identities; the PNT-feedback append adds11
actual source/audit modules to make734. The Box–Lee comparison adds two modules
above723; the NL comparison and actual prime-count consumer add three above734.
Their union has739 compiler module identities, including audits and adapters;
this is not a count of739 new theorems. These scoped replays overlap.

Use Linux x86-64 with Python3.11, Git, `cc`/GCC, GNU `time`, `prlimit`, `taskset`
and the pinned Lean4.34.0-rc2 toolchain. The compiler's SHA-256 must be
`e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`.
The scripts reject a different compiler. The included root `lake-manifest.json`
and generic reference list all nine dependency URLs and exact commits; Mathlib is
`71a80585ee495fc24472fd0eaffc89d94e4fd8d6`.
Install `mpmath==1.3.0` for deterministic proposal regeneration. It is not trusted
as a mathematical premise: its generated numbers must pass the Lean kernel.

The following commands use fresh absolute paths. Replace `PACKET`, `SCRATCH`,
`LEAN` and `CPU` with the actual packet root, an experiment-owned scratch
directory, the pinned `lean` executable and one available CPU number. An existing
output directory is rejected. There are no random seeds: all numerical data is
deterministic.

```sh
export PYTHONDONTWRITEBYTECODE=1
python3 -B PACKET/source/Solutions/RHOcticPush.v1/integration/continuation/bootstrap_generic.py \
  --compiler LEAN --cpu CPU --out SCRATCH/generic
export IEANTN_GENERIC_CONTEXT=SCRATCH/generic/GENERIC_CONTEXT.json

python3 -B PACKET/source/Solutions/RHOcticPush.v1/integration/continuation/regenerate_moments.py \
  --out SCRATCH/regenerated-moments

python3 -B PACKET/source/Solutions/RHOcticPush.v1/integration/continuation/finish_clean_single_lane.py \
  --source-packet PACKET --context SCRATCH/generic/GENERIC_CONTEXT.json \
  --primary SCRATCH/primary454 --out SCRATCH/clean723

python3 -B PACKET/source/Solutions/RHOcticPush.v1/integration/feedback/reproduce.py \
  --foundation SCRATCH/clean723/ram60611 --out SCRATCH/feedback734

python3 -B PACKET/source/Solutions/RHOcticPush.v1/integration/feedback/reproduce.py \
  --verify SCRATCH/feedback734
python3 -B PACKET/source/Solutions/RHOcticPush.v1/integration/feedback/controls.py \
  --run SCRATCH/feedback734 --out SCRATCH/feedback734-controls

python3 -B PACKET/source/Solutions/RHOcticPush.v1/comparisons/reproduce_box_lee.py \
  --foundation SCRATCH/clean723/ram60611 --out SCRATCH/box-lee
python3 -B PACKET/source/Solutions/RHOcticPush.v1/comparisons/reproduce_box_lee.py \
  --verify SCRATCH/box-lee
python3 -B PACKET/source/Solutions/RHOcticPush.v1/comparisons/test_box_lee.py \
  --run SCRATCH/box-lee --out SCRATCH/box-lee-controls

python3 -B PACKET/source/Solutions/RHOcticPush.v1/comparisons/reproduce_nl_parabolic.py \
  --foundation SCRATCH/feedback734 --out SCRATCH/nl-parabolic737
python3 -B PACKET/source/Solutions/RHOcticPush.v1/comparisons/reproduce_nl_parabolic.py \
  --verify SCRATCH/nl-parabolic737
python3 -B PACKET/source/Solutions/RHOcticPush.v1/comparisons/test_nl_parabolic.py \
  --run SCRATCH/nl-parabolic737 --out SCRATCH/nl-parabolic-controls
```

Keep `PYTHONDONTWRITEBYTECODE=1` or use `python3 -B` on **every** invocation.
The source packet is immutable and its inventory includes only registered source
files. Import-generated `__pycache__` files correctly make its exact-inventory
preflight fail. Do not weaken that check. The final output directory is separate
from the source packet.

The clean723 coordinator first compiles the261-module baseline,55-module
spectral extension and24-module canonical core, then114 new sources,165 moment
and consumer sources,40 Box-zero sources,33 closed-Box sources,19 signed-spectral
sources and11 Ramanujan synthesis sources. Its last validator recursively reads
back the entire source/object/log/C-resource chain. Each application object is
freshly compiled from the included source; only the explicit pinned generic
libraries are reused. No developer overlay or historical application bank is
accepted as a generic dependency.

The single-lane coordinator is the original reviewed coordinator with exactly
one resource-only change: supplement concurrency is reduced from at most4 to1.
`RESOURCE_VARIANT.json` records the old/new hashes and exact line. No numerical
algorithm, source statement, proof checker or mathematical assumption changes.
The standalone bootstrap clones the nine pinned public generic sources into
owned scratch, runs the pinned Mathlib cache tool, confirms every Git revision
and clean tracked source, then actually imports complete Mathlib. It does not
require the earlier failed application run or any old application objects.

The scripts preserve512GiB of host RAM and check available RAM separately from
disk. The main compiler lanes have64GiB address-space caps; those caps are not
measured physical RAM. Initial setup requires at least1TiB of free disk and the
owned scratch limit is300GiB. This is intentionally a high-resource reproduction
policy, and a smaller machine may reject admission rather than producing an
unreliable run. The separate large exact prime-count reproduction has its own
128/256GiB address-space limits and cold-foundation procedure; it is not silently
included in the739 analytic module union.

The octic proposal generators live under `moments/endpoint/`: deterministic
endpoint/log enclosures, cell caps, block proofs and final assembly are preserved.
They reproduce the7,301 endpoints and7,300 integration cells. Generated numbers
are proposals until the actual Lean kernel proofs recheck them and their finite
and infinite-integral adapters. The C logarithm workload and coefficient
source/build/run associations are executed by the included primary controller.
The existing source-model applicability and compiler/runtime/OS/hardware
contracts remain explicit; the Python harness and ordinary kernel certificates
are not called source-first PV.

`regenerate_moments.py` actually writes the five generated data/proof families
in fresh scratch, compares every one of the128 frozen mathematical source hashes
and all three proposal JSON files, then executes all five generator `--check`
CLIs in normal, `-O` and `-OO` modes. The formal build uses the byte-identical
immutable packet copies; no proposal file is introduced as an unchecked theorem
premise. The full Lean pipeline remains a separate required stage.

Every accepted run records exact source, object, command, include-resource and
log hashes, compiler/dependency identity, elapsed time, memory measurements and
owned disk scope. Standard-axiom audits inspect actual proof values, not merely
imports or theorem statements. The canonical734 final audit covers all83 new
canonical proofs, four combined consumers and three source-comparison roots;
the exact11 new theorem types are separately compiled. Official Comparator
receipts require a compatible approved worker and are not fabricated by these
scripts.

The Box–Lee source comparison proves its full displayed functions compare
strictly for every real logarithm parameter at least35. The NL scalar comparison
holds for parameters at least24, and its actual prime-count consumer has the
additional explicit condition that the left endpoint is at least exp(24).
The original written NL analytic result retains its original status and
hypotheses. Neither comparison establishes a global best-known record.

The three current validator control suites make69,18 and24 actual CLI decisions,
respectively. Every mode has a distinct raw output path. Earlier Box–Lee and NL
control attempts used colliding labels for the two optimized Python modes;
their receipts are preserved as historical or partial evidence, with separate
corrected reruns. The scientific source and accepted proof results did not change.

Do not change the generic context between execution and historical readback.
The prefix receipts bind actual dependency-output paths as well as source hashes;
substituting a different generic library directory correctly rejects that
association. A newly created reproduction uses its own consistent context from
start to finish. Historical failed/interrupted receipts remain separate.

After completion, preserve the exact source/manifests/commands/statements,
accepted proof receipts and artifact hashes. Delete only experiment-owned,
verified-regenerable duplicate data or caches after a preview and readback.
Never delete original research sources, locked numerical inputs, the sole copy
of an essential certificate or accepted proof artifacts. The top-level evidence
index records which clean runs actually passed; the existence of this README or
an executable command is not itself an execution receipt.
