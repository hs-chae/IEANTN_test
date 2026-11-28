# Clean original-checker replay with independent physical-memory supervision

This route starts the original, unchanged `reproduce_fft_dag_v2.py` in a fresh
source-cold directory. It does not depend on any historical continuation or
reuse its application proof objects. The fixed producer must first regenerate
all original candidate Lean/CSV bytes and match the public expected inventory.
The original controller, checker mathematics, algorithms and target remain
unchanged. This numerical route is kernel certificate verification; complete
source-first C PV additionally needs the separately compiled actual main and
ANT consumers.

Use `reproduce_fft_dag_physical_v2.py` with `--worker-virtual-as unlimited`.
It executes the unchanged checker through explicit `prlimit --as=unlimited`.
For N24 it first requires an actual owned300GiB/noSwap cgroup. The independent
existing resource supervisor remains responsible for separate availableRAM and
free-disk admission (1TiB each),256GiB host reserve, and the original campaign
scratch admission/guard. Unlimited virtual address space is not an increased
physical-memory or scratch allowance.

```sh
python3 -u Solutions/RH080Next.v1/dual/reproduce_fft_dag_physical_v2.py \
  --context /pinned/context.json --candidate /regenerated/candidate \
  --run /fresh/source-cold/run --workers 12 --worker-virtual-as unlimited
```

Keep this exact argument order in the source-pinned production command manifest.
`--prepare-command` prints the precise future `prlimit`/Python vector, but neither
executes it nor creates acceptance. The old AS300 wrapper and all old evidence
remain unchanged.

After actual successful compilation and completed resource evidence, run
`verify_fft_dag_fresh_v3.py` under normal Python, `-O` and `-OO`, with `--run`,
`--context`, `--candidate`, `--output`, `--supervisor`, `--command-plan`, `--stdout`,
`--stderr` and the exact owned `--unit`. The gate checks the original source-cold
plan, every compiler/source/object/data association, full typed axiom audit,
actual source-pinned unlimited-AS wrapper command and actual300GiB/noSwap
supervisor evidence. Its `--proof-only-toy` exception is restricted to S13 and
cannot admit production N24.

`export_fft_dag_fresh_bank_v3.py` takes `--base`, `--context`, `--candidate`,
`--accepted` and a fresh `--run`, producing immutable source/object/data hardlinks.
It independently verifies the actual fresh gate identity and mathematics before
calling the preserved format adapter. This export performs no new compilation
and is never the proof itself. Use `--toy` only for bounded S13 test fixtures.

The new resource-reader controls use explicitly synthetic fixtures, separate
from mathematical or physical-run evidence. Actual small wrapper replays, gate
rejections and format exports have separate receipts. A successful bounded
control does not establish that the entire large1033-module clean route has run.
The exact source bundle and final report must distinguish completed bounded
controls, the historical1031+2 continuation, and any full new source-cold replay.

The wrapper optimization modes apply to its own actual CLI. Its preserved exec
vector deliberately starts the unchanged original checker with its existing
Python options; do not describe the original checker as running with inherited
`-O` flags. The independent acceptance gate itself is explicitly exercised in
all three optimization modes.

The completed bounded workload is ONE normal S13 source-cold replay:120 modules,
18 typed standard-axiom roots,1117.719 seconds, and maximum compilerRSS34523508KiB.
The normal mathematical child exited before the outer three-mode test controller
was intentionally stopped; full optimized checker replays were not performed.
Its independently rechecked normal proof, command-only wrapper and format
exports pass under all three new-interface optimization modes. Separate actual
fresh-gate mutations and explicitly synthetic physical-resource mutations also
reject in all three modes. The bounded normal run has no retained owned-cgroup
OOM counter, so its successful exit is not reported as a measured zero counter.
