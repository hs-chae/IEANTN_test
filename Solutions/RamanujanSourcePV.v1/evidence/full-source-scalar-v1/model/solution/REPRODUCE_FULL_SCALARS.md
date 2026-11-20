# Reproduce the full finite scalar certificate

This experiment proves **only** strict integer row inequalities, real e/log
bounds, and exact coverage for all1,755,663 original cells. It does not prove
that their prime-count fields equal actual prime counts. It is kernel-only
numerical verification, not source-first PV by itself. The separate C execution
extension must preserve this distinction.

The accepted result is in `evidence/full-scalars-kernel-v1/RESULT.json`; its
SHA-256 is a66c451b8e84aafd5f0bb9ccc93aecafd65381457d8c9cd4a541a78b9e941287.
The compact summary records859 generated source modules plus an independent
exact-type audit,1548.30seconds wall time,18,284.03 selected CPU-seconds and
6.96GiB largest measured worker RSS. No worker failed. The aggregate/disk
sampler began after the computation started, so its maxima are not full-run
peaks. Original prime-count data and assumptions have not been changed.

Use Linux x86-64, the exact pinned Lean/compiler and generic dependency commits
in BUILD_CONTEXT.json, and Python3.11. No random generator is used. Obtain the
repository and generic caches as described in README. Choose a fresh adequately
provisioned storage directory. The following example uses `/data/replay-rpv`;
change that prefix and the CPU list to genuine available resources on your host.
The numerical scratch directory must retain the explicit final component below.
Run from this solution directory:

```sh
python3 scripts/bootstrap_context.py --out /data/replay-rpv/GENERIC_CONTEXT.json
python3 scripts/reproduce_numerics.py \
  --scratch /data/replay-rpv/native/ivy-ramanujan-source-pv-20261119 \
  --study /data/replay-rpv/native-study
python3 scripts/reproduce_lean.py \
  --context /data/replay-rpv/GENERIC_CONTEXT.json \
  --out /data/replay-rpv/core --root RamanujanPV.FullFiniteScalars --cpus 52,53,54,55
```

The first output's parent must already exist; the other experiment directories
must be fresh. The numerical procedure clones/builds the pinned native backend,
regenerates the64 adaptive binary chunks and checks all counts independently.
Its native result is not a formal count proof. The core command creates a
fresh application bank; it does not use the old application path recorded in
the historical BUILD_CONTEXT.json. Point subsequent compilation to that bank:

```sh
python3 - <<'PY'
from pathlib import Path
import json
root = Path('/data/replay-rpv')
context = json.loads((root / 'GENERIC_CONTEXT.json').read_text())
context['new_application_object_root'] = str(root / 'core/lean')
target = root / 'core/CONTEXT.json'
if target.exists():
    raise ValueError('fresh context output required')
target.write_text(json.dumps(context, indent=2) + '\n')
PY
python3 scripts/generate_full_scalar_certificate.py \
  --run /data/replay-rpv/native-study/evidence/finite-actual-1490000000000/RUN.json \
  --certificates /data/replay-rpv/native/ivy-ramanujan-source-pv-20261119/finite-actual-1490000000000 \
  --out /data/replay-rpv/core/full-scalars --name FullAdaptiveScalars \
  --rows-per-block 4096 --proof-chunk 512
python3 scripts/execute_full_scalar_certificate.py \
  --manifest /data/replay-rpv/core/full-scalars/PROPOSAL.json \
  --native-run /data/replay-rpv/native-study/evidence/finite-actual-1490000000000/RUN.json \
  --context /data/replay-rpv/core/CONTEXT.json \
  --out /data/replay-rpv/core/full-scalars-run \
  --jobs 12 --memory-gib 24 --cpus 52,53,54,55,56,57,58,59,60,61,62,63
python3 scripts/execute_full_scalar_certificate.py \
  --check /data/replay-rpv/core/full-scalars-run/RESULT.json
```

Before compiling, the controller independently joins every generated seven-word
literal and every tree pivot against the original binary rows. It then compiles
every Data/Check/Final source into the fresh bank and independently compiles the
exact final ScalarCertificate type. Acceptance requires all requested receipts,
current source/object hashes, exact domain endpoints and actual standard-axiom
reports. A failed worker writes FAILED.json and cannot publish final acceptance.
The validators use explicit checks and are tested under normal/-O/-OO Python.

The combined worker ceiling is288GiB; the separate192GiB final audit runs after
the worker pool drains. These are address-space limits, not measured peak RSS.
The controller requires genuinely available1TiB RAM and preserves512GiB host
reserve. Independently verify free disk before using up to300GiB scratch. A small
profile may use `--limit-rows 32` in generation and `--allow-profile` at execution;
that profile is not a replacement for the full run.

The original full run and32-row controls have actual receipts. This complete
clean-directory recipe has not been rerun as a single fresh end-to-end wrapper;
its constituent numerical regeneration and full kernel verification were run
and independently checked separately. Do not infer a new isolated-workflow
receipt from these instructions. Keep accepted proof artifacts and inputs until
their deterministic regeneration has actually been checked before any cleanup.
