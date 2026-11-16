# Actual main-frame, exact C-expression weights and conditional PNT replay

This source-only component appends **859 application modules and 3,262 selected
theorem roots** to the unchanged **1,412-module, 2,350-root** base component.
The complete finite graph has **2,271 modules and 5,612 distinct selected roots**.
No application objects are shipped. All original C, interval algorithms,
parameters and analytic hypotheses are preserved.

The final statement is the existing bound
**Eπ(x) ≤ 0.008441646 · x⁻¹⁄⁸ for x ≥ exp(330)**, under exactly the explicit
analytic hypotheses in `source/SourceMainWeightsV1/PNT.lean`. In particular this
remains conditional on the original PrimaryInputs, CHJ, zero-count/low-zero,
finite-height RH and QRH inputs. No new numerical or analytic axiom is added.

The new graph includes 768 original framed point executions, 24 framed point
aggregators, 24 kernel-checked exact numerical weight chunks, their real-domain
correctness proofs and the final conditional ANT consumer. The numerical weight
checks alone are kernel verification; they are not source-first PV by themselves.
The source consumer uses actual source-framed point-output proofs. **Complete
main-loop accumulation, startup, final I/O/flush and observed whole-executable
association are still separate obligations.** This component must not be called
completed verification of the entire executable.

## Clean environment

Use Linux x86-64 and Python 3.11 or later, with Git, `/usr/bin/time`, and the exact
Lean toolchain and public mathlib/package commits in `SOURCE_LOCK.json`. The
unchanged bootstrap documents and checks their full identities. Install the
pinned Lean distribution and public library caches, then run:

```sh
python3 -OO base/prepare_environment.py \
  --toolchain /absolute/path/to/lean-4.34.0-rc2-linux \
  --mathlib /absolute/path/to/pinned/mathlib \
  --out /absolute/path/outside-this-capsule/environment.json
```

No old IEANTN application build, object bank, or developer workspace is needed.
Generic compiler/core-runtime and public library caches are explicit trust
inputs. The append validates their versions and commits again.

## Full reproduction

Run within a host-managed resource scope that preserves adequate host resources.
The owner authorized up to 300 GiB aggregate study RAM after checking actual RAM,
independently of disk space. The obsolete 4 GiB cap is not used. A practical
reservation for the final append is up to 256 GiB/16 CPUs; the frame phase uses
14 workers and the later weight phase six workers, with no overlap of those two
heavy groups. These are explicit configurable job counts, not performance claims.

```sh
python3 -OO reproduce_all.py \
  --environment /absolute/path/environment.json \
  --out /absolute/path/fresh-run \
  --base-jobs 8 --jobs 14 --frame-jobs 14 --weight-jobs 6
```

This regenerates the actual C and numerical source outputs, checks their source
and numerical-word associations, compiles all base application proofs, then
compiles every append source and audits all 5,612 final root closures. Successful
receipts are written atomically only after all checks pass. Python `-O`/`-OO`
does not disable any acceptance check.

To append to an already completed **identical fresh base run**, use:

```sh
python3 -OO reproduce_append.py \
  --environment /absolute/path/environment.json \
  --base-run /absolute/path/completed-base-run \
  --out /absolute/path/fresh-append-run \
  --jobs 14 --frame-jobs 14 --weight-jobs 6
```

The completed base run must retain its `RECEIPT.json`, `VALIDATOR_PINS_V1.json`,
proof receipt, all proof logs and all 1,412 freshly source-built application
objects. The append checks every source/object/log hash, every base compile
exit, exact selected root population, compiler identity and standard-axiom
closure. It rejects partial, warm, missing or mismatched base receipts. Only
that source-built base bank and this append's initially empty object bank are
application entries on `LEAN_PATH`; old developer banks are excluded.

## Controls and evidence

```sh
python3 -OO check_controls.py \
  --environment /absolute/path/environment.json \
  --out /absolute/path/fresh-controls
```

The actual CLI controls cover normal, `-O` and `-OO` modes, invalid job counts,
unknown flags, existing output, missing base acceptance, native/admitted proof
diagnostics and real pinned-source corruption. These tests do not replace Lean
proof builds or count as mathematical completion.

`PROVENANCE.json` records the immutable base archive and all source origins.
Six inherited main/math source variants differ only in the already recorded
kernel proof/options/comment changes. Their original bytes and explicit diffs
are retained under `provenance/`; the unchanged base selects its existing
native-free versions. Original host receipts under `evidence/original-host/`
are provenance, not clean replay acceptance. `prepare.py` is a maintainer
snapshot utility and is not needed for clean reproduction.

## Receipts, resources and cleanup

`PROGRESS.json` and `CHECKPOINT.json` preserve partial progress. They are never
acceptance receipts. The final receipt records every actual compile command,
source/object/log hashes, duration and complete final axiom audits. Host resource
scope receipts separately record charged RAM, individual compiler RSS, elapsed
time, disk measurements and OOM events; uninstrumented peaks must be disclosed.

After a completed replay and its reproducibility checks, large regenerable
fixture copies, raw numerical arrays, generated C binaries and caches may be
removed only from verified experiment-owned directories, with a cleanup preview
and receipt. Preserve sources, locks, scripts, hashes, accepted proof artifacts,
essential certificates and verification receipts. This recipe never deletes
unrelated directories or silently prunes the accepted base object bank.

The source-to-AST render proofs, formal application execution, arithmetic and
mathematical consumers are checked by Lean's kernel. The pinned compiler,
generic runtime/API, operating system and hardware remain disclosed execution
trust boundaries. This is host source-cold replay, not a claim of final namespace
isolation or verified compilation of the generic toolchain.
