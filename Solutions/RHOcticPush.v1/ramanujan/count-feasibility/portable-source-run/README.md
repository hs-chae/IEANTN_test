# Reproduce the count and actual source-model consumer

This is an additive source-only composition of the existing numerical generator,
pure kernel checker, C counter, high-input main, independent bounded C11 surface
grammar and mathematical execution model. The C programs, ASTs, numerical target,
90,670,946-record certificate format and mathematical assumptions are unchanged.
The older conservative recipe in `../portable/` remains preserved.

The fixed full target is `Nat.primeCounting 1490000000000 = 55206486339`.
The source-facing conclusion constructs an inhabited execution of the two actual
C source texts whose model output is the eight little-endian bytes of that value;
a separate theorem covers every successful modeled execution. Generic compiler,
C-model applicability, ABI/runtime, stdio/OS and hardware contracts remain
explicit. Surface-syntax soundness does not prove general ISO-C semantic adequacy.

## Prerequisites

Use the pinned Lean4.34.0-rc2 compiler and Mathlib revision
`71a80585ee495fc24472fd0eaffc89d94e4fd8d6`, with the other exact generic dependency
revisions in the campaign's setup/GENERIC_CONTEXT instructions. The context JSON
must refer only to those generic libraries, with no application proof-object bank.
Pass its actual clean-environment path through `--context`. Python3.11, Git,
GNU time, taskset/prlimit and the pinned source files in this repository are used.
No old experiment checkout or historical application objects are execution inputs.

Full execution uses substantial resources: inspect actual RAM and free disk
separately before starting. The resource-only engine permits up to22 workers,
keeps a512GiB host reserve, and accounts for live jobs' potential physical growth.
Numerical parts have128GiB virtual-address limits and large final audits256GiB;
these are per-compiler address ceilings, not measured aggregate RAM. The initial
full engine admission requires genuinely available1TiB RAM. A512GiB reserve plus
actual job cap is also checked by the approved proposal generator, whose only
change is the documented resource-admission line. Never fabricate MemAvailable.

## One command from clean source

From the repository root, using a fresh experiment-owned output directory:

```sh
python3 Solutions/RHOcticPush.v1/ramanujan/count-feasibility/portable-source-run/reproduce.py \
  --context /absolute/path/to/GENERIC_CONTEXT.json \
  --out /large/experiment-owned/count-source-run \
  --jobs 22 --cpus 64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85
```

Choose available CPU IDs appropriate to the actual host. Do not share the output
with any other run. The command regenerates the numerical data, checks the full
locked source and packed-data identities, overlays the exact accepted source-model
and grammar modules, and compiles all selected mathematical consumers once.
Same-named source collisions are allowed only with identical full source hashes.
No generated CSV, stored native result or mathematical target is imported as an
unproved axiom. Every gap and arithmetic part must pass actual Lean kernel checks.

The new physical scheduler addresses the older clean route's conservative
sum-of-virtual-address restriction, which permitted very few128GiB tasks. It is
not a program-algorithm or numerical-parameter change and is not a controlled
speedup claim. Actual wall time, child peak RSS, sampled process RSS, disk,
interruptions and proof receipts are recorded by the respective scopes.

## Bounded workflow control

```sh
python3 Solutions/RHOcticPush.v1/ramanujan/count-feasibility/portable-source-run/reproduce.py \
  --context /absolute/path/to/GENERIC_CONTEXT.json \
  --out /large/experiment-owned/count-source-smoke \
  --smoke --jobs 1 --cpus 64
```

The smoke mode proves only `pi(1000)=168` and checks the original high-input
program's parameterized source/model and independent grammar. It does **not**
prove the high-input numeric output; its exact-count argument remains explicit
in that generic source-model theorem. The smoke proof uses48GiB address limits.
It is a workflow test, never a replacement or weaker accepted version of the
fixed high-count experiment.

## Read back a completed run

```sh
python3 Solutions/RHOcticPush.v1/ramanujan/count-feasibility/portable-source-run/reproduce.py \
  --check /large/experiment-owned/count-source-run
```

The outer reader independently reconstructs all source recipes and the entire
selected application import closure. It checks source/object/log ownership,
actual compiler commands, included C bytes, address caps and measured resources,
complete dependency probes, empty numerical axioms, standard mathematical axioms,
and the final source/count proof-value graph. A source file merely imported or
read is not counted as proof consumption. Normal, `-O` and `-OO` mutation tests
are separate reader evidence.

## Current evidence and cleanup

Consult the immutable run receipts and ACTIVE_HANDOFF for actual execution
status. At this documentation checkpoint the new fast route is prepared for a
small actual smoke run; no second90-million-record high replay has been launched.
The full high mathematical result is established only when the separately
recorded source-built current-campaign parts, cold695+299 complement, unchanged
Final and new source-indexed consumer all pass. Do not infer a completed full
clean fast run from a small smoke control or script availability.

Retain scripts, exact parameters, source and dependency pins, concise results,
all essential proof/receipt hashes and unique accepted artifacts. After a run and
its regeneration procedures are actually checked, remove only previewed,
experiment-owned, reliably regenerable large duplicates or caches. Never remove
original sources, locked inputs, accepted proofs or the only reproducibility copy.
