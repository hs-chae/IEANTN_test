# Clean combined-provider reproduction

This additive entry point regenerates and checks the exact 554 application
sources for the combined certified-prime-list and balanced-4096-data proof.
The completed incremental theorem remains the same: the Ramanujan gap exceeds
501,901 for every real input from 38,358,837,683 inclusive to 38,359,837,684
exclusive. The existing 548/549-source experiment and its replay are unchanged.

The accepted 27.202-second Queries build recomputes the 285 P-prefix checks
and assembles the source-count providers; it reuses the accepted Q-prefix
proofs. It is not a new timing for recomputing both query families.

The new complete clean proof replay is **not yet executed**. Source preparation,
all-mode plan controls and the already completed incremental proofs have
separate receipts; a prepared source tree is not a mathematical success.

Use the owner repository and commit recorded by the publication manifest, with
the source/evidence supplement. Follow `REPRODUCE_PACKED_MILLION.md` and
`REPRODUCE_COUPLED_ANALYTIC.md` to install the pinned generic dependencies and
create an isolated context using `scripts/bootstrap_context.py`. The pins are
Lean 4.34.0-rc2 and Mathlib commit
`71a80585ee495fc24472fd0eaffc89d94e4fd8d6`. The accepted generators use Python
3.11, Sympy 1.14.0 and mpmath 1.3.0, with a C++ compiler. No historical
application proof-object bank or data-only `/data` source path is required.

Choose one shared experiment root and create it before generating a context.
Put this study's context, outputs, source-generation scratch and proof bank
beneath that same root, so the disk guard counts them together. In a **fresh
reproduction checkout**, from this solution directory:

```sh
mkdir -p /data/ieantn-ramanujan-reproduction
python3 scripts/bootstrap_context.py \
  --out /data/ieantn-ramanujan-reproduction/combined-context.json
python3 - /data/ieantn-ramanujan-reproduction <<'PY'
from pathlib import Path
import json, shutil, sys
root = Path(sys.argv[1]).resolve()
context = root / 'combined-context.json'
canonical = Path('BUILD_CONTEXT.json')
shutil.copyfile(canonical, root / 'BUILD_CONTEXT.original.json')
value = json.loads(context.read_text())
value['new_application_object_root'] = str(root / 'lean')
context.write_text(json.dumps(value, indent=2) + '\n')
shutil.copyfile(context, canonical)
PY
```

`bootstrap_context.py` relocates compiler/generic-library paths while preserving
their pinned compiler hash and dependency revisions. It does not relocate the
owned scratch root. The explicit metadata step above sets that root in both
the supplied context and the clean checkout's canonical `BUILD_CONTEXT.json`:
the frozen backend reads the canonical copy for its admission guard. This
locally changes a tracked configuration file in the reproduction clone, not
the original published scientific inputs or active research checkout. The
original canonical metadata is saved in the shared root. Do not perform this
step in the running research checkout. Source locks and script/C payload pins
do not hash the canonical context's whole bytes; compiler and generic revision
pins must remain unchanged.

Run the full clean recipe using fresh output directories:

```sh
python3 scripts/reproduce_prime_base_combined.py \
  --context /data/ieantn-ramanujan-reproduction/combined-context.json \
  --out /data/ieantn-ramanujan-reproduction/combined-clean-full \
  --jobs 6 --cpus 84,85,86,87,88,89
python3 -OO scripts/reproduce_prime_base_combined.py \
  --check /data/ieantn-ramanujan-reproduction/combined-clean-full
```

Choose unused CPU cores and fresh owned output paths. The default first calls
the unchanged `reproduce_packed_million.py --bound-result --plan-only` to
regenerate the original source data. It next runs the published
`generate_prime_base_mask_scout.py` and `generate_balanced_mask_data.py` to
regenerate the exact `BaseP`, `CombinedP` and standalone
`W4096DataOnly.Data` sources. These generators create untrusted proposals;
their kernel equalities must compile. They use no random seed. Unneeded
calibration modules are not in the selected combined build closure.

`evidence/prime-base-combined-clean-v1/SOURCE_LOCK.json` fixes all 554 source
hashes, import edges, C payloads, compiler identity and dependent script hashes.
It derives from the preserved original 549-source lock, removing its old P
mask and original Queries/Million/Result modules and adding nine new
generic/data/base/consumer modules. The ordinary Q computation, all 285 rows,
source anchors, numerical values, assumptions and six C bindings are unchanged.
Incidental original raw-data imports remain; old local-primality/Lucas proof
providers and the old P-mask equality are excluded from the selected proof.

The final stage invokes the unchanged guarded proof backend with a fresh
application object directory, targeting
`PrimeBaseCombinedIndependentAudit` and the three exact
`PrimeBaseCombinedResult` binding/interval/gap theorems. Every application source
and the independent final audit must compile; only pinned generic libraries are
reused. The resource policy requires at least 1 TiB genuinely available RAM,
512 GiB host reserve, separately at least 1 TiB free disk, at most 300 GiB owned
scratch and at most 300 GiB aggregate worker reservations. Previously measured
96/192 GiB module profiles are retained. The original source-preparation
frontend checks 15 GiB forecast headroom; the proof scheduler checks its
separate 3 GiB forecast and pauses new work when resources fall. On a stop
signal, source preparation finishes its current child, and an initialized
proof scheduler drains its active workers. Partial work is never acceptance.

For the tested source-only route, append `--plan-only` and then use
`--check-plan OUTPUT_DIRECTORY`. This checks exact regenerated/staged sources,
the full script/command ledger and executable future workload. It does not run
Lean. Optional `--prepared-root` reuses an exact regenerated original source
tree, while still regenerating the combined support sources and checking every
byte. This is explicitly source reuse, never proof-object reuse. The full
`--check` additionally checks the actual backend module population, selected
theorems, final receipt and complete source/object/axiom readback.

The plan controls are reproducible using an actual default plan-only output:

```sh
python3 scripts/test_prime_base_combined_repro.py \
  --normal-prepared /data/ieantn-ramanujan-reproduction/combined-plan-normal \
  --out /data/ieantn-ramanujan-reproduction/combined-plan-controls \
  --context /data/ieantn-ramanujan-reproduction/combined-context.json \
  --cpus 10,11
```

The harness checks the preceding normal-mode default generation. In `-O` and
`-OO` it regenerates the combined support sources and stages/checks the exact
original source tree produced by that normal run; this source reuse is
explicitly recorded and imports no proof objects. It exercises positive plan
readbacks and rejects missing command/pin populations, wrong source/lock/
frontend/theorem identities, unrelated backend commands, duplicate keys,
nonfinite JSON and attempts to call a plan a completed proof. It temporarily
modifies only its inactive experiment-owned control receipts, saves and
restores their exact original bytes, and checks positive readback again.

Supporting accepted sources and receipts are in
`evidence/prime-base-mask-scout-v1/`,
`evidence/packed-mask-balanced-data-v1/` and
`evidence/prime-base-combined-consumer-v1/`. The prime-list fold and balanced
codec are kernel computations. Source-first PV belongs to the unchanged
source-linked C checker/counter/e/log/cell programs and their mathematical
consumers. This recipe does not prove a new native C codec, a stronger ANT
theorem, physical loading, an unverified native caller, or process-output
association beyond the existing documented boundary.
