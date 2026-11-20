# Guarded isolated coupled-source replay

`reproduce_guarded_coupled_closure.py` is an additive copy of the existing
profiled clean-build helper. It resolves the exact selected source closure and
rebuilds every application module into a fresh object bank. Only the pinned
generic libraries and Lean core are reused. The original helper and the three
running high-count controller/observer files are unchanged.

Use the same CLI as `reproduce_profiled_closure.py`. The approved coupled run
uses two workers,48GiB per process,96GiB aggregate,CPUs8–9 and512GiB host reserve.
Each dispatch and every polling cycle checks real available RAM≥1TiB and≥512GiB
plus already reserved and proposed allowances. Disk is checked independently:
free≥1TiB and the entire owned experiment’s allocated bytes plus3GiB forecast
must remain≤300GiB. Measurements precede submission; reservations are recorded
before submitting workers. Low resources pause new dispatch while active proofs
drain; dispatch resumes only when the measured policy holds again.

SIGUSR1,SIGTERM or SIGINT requests a clean checkpoint: no further proofs are
submitted, every already active proof finishes, and all successes and failures
are preserved. A proof failure likewise stops new dispatch and drains every
active worker before writing the checkpoint. No compiler is killed by this
helper. Checkpoint status is never mathematical acceptance.

Only after the complete source closure and fresh named axiom audit pass does
the helper validate a pending result and atomically publish RESULT.json. It
independently rereads sources, objects, logs, source/compiler/context pins,
resource caps and the full reservation journal. `--check RUN_DIRECTORY` is a
read-only recheck. This numerical/build harness is not itself source-first PV.

Final helper SHA256:
`292e87eb0078a2dd31dade54bf7a9933e98989cb29516c0ccc2c108550ca8661`.
Actual normal/-O/-OO controls are preserved in
`evidence/guarded-coupled-cold-controls-v2/PACKET.json`:33 CLI routes, three
actual two-module cold builds plus final auditors, actual SIGUSR1 drains,
and actual failed proofs alongside concurrently successful proofs. Every
active successful compiler receipt is retained. Physical host exhaustion was
not induced; actual available-memory/disk positives and explicit invalid
resource policies were tested.

The full coupled-source cold run is separate from these tiny controls. Its
actual PLAN,source lock,commands,progress and eventual RESULT determine its
status; existence of this helper or its controls is not evidence that the
full replay has completed. No full finite-count completion is implied.
