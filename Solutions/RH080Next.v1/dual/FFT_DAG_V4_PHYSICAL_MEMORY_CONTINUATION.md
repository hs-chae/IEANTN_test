# V4: unchanged numerical proof with an independent physical-memory limit

V4 is an additive resource-only continuation. It preserves the exact original
candidate, input, algorithm, all generated Lean and CSV bytes, checker statements,
1031 successful compiler receipts and their three distinct origins. It does not
relabel a certificate proof as source-first PV. Actual C-to-ANT consumers remain
a subsequent, separately audited requirement.

The failed v2 Final compilation exhausted virtual AS256GiB while its measured
peak compiler RSS was141287720KiB. The completed owned physical300GiB cgroup had
no OOM or kill event. Virtual mappings and committed physical memory differ.
V4 therefore requests `prlimit --as=unlimited` explicitly, retaining the existing
physical300GiB/noSwap cgroup and independent supervisor's separate RAM/disk
admission, host reserve and campaign scratch guards. This is not permission to
raise physical RAM or scratch limits. N24 also checks its actual owned
300GiB/noSwap cgroup before validating any prefix.

The frozen v3 lineage validator is reused unchanged; the failed or interrupted
v2/v3 Final output is never accepted as a successful receipt. Only the1031
successful modules (992 original, four first-continuation,35 nested-continuation)
are inherited. The two remaining unchanged modules must actually compile.

Use a fresh directory and this exact argument order. The independent reader
checks the actual vector; it does not rewrite historical executed commands.

```sh
python3 -u Solutions/RH080Next.v1/dual/resume_fft_dag_source_cold_v4.py \
  --context /pinned/context.json --candidate /fixed/candidate \
  --prefix /original/source-cold/run --continuation /first/continuation \
  --nested-continuation /v2/continuation --run /fresh/v4/run \
  --workers 12 --worker-virtual-as unlimited
```

The source-pinned production command manifest must contain:

```json
{"phases":{"original_source_cold":992,"prior_continuation":4,
"prior_nested_continuation":35,"new_compilation":2},
"original_outcomes_unchanged":true}
```

It must also pin the v4 controller, unchanged v3 lineage helper, exact independent
supervisor and all executed dependencies. Plan and result use schema4,
`per_compiler_AS_bytes:null` and
`per_compiler_AS_policy:"EXPLICIT_RLIM_INFINITY_WITH_SEPARATE_PHYSICAL_CGROUP"`.
No new mathematical premise or generalized zero-summation premise is introduced.

`verify_fft_dag_nested_resume_v4.py` independently checks every source, literal,
object, typed final statement, standard axiom closure, per-module compile origin,
actual resource command and completed supervisor evidence. It requires the
concrete owned unit, both actual300GiB/noSwap endpoints, nondecreasing OOM counters
with no OOM/kill, separate1TiB RAM and disk admission,256GiB host reserve and
original270/290GiB scratch admission/guard. Its normal, `-O` and `-OO` invocations
must pass before `export_fft_dag_bank_v4.py` makes an immutable hardlink bank.

`watch_fft_dag_nested_completion_v4.py` performs those three independent gates
and the format-only export after real successful supervisor and mathematical
results exist. Its options match the older observer: `--run`, `--context`,
`--candidate`, `--supervisor`, `--command-plan`, `--stdout`, `--stderr`, `--unit`,
`--observer`, `--export`. Use fresh observer/export paths. An incomplete child
produces no acceptance or export. The observer never controls the proof worker.

Bounded tests actually compiled a cheap S13 typed audit with explicit unlimited
AS in all three Python modes, checked three complete historical lineages, made
three format exports and rejected24 prefix mutations. The real resource reader
also passed three explicitly synthetic canonical-command controls and rejected
60 synthetic resource/argv mutations; these fixtures are not physical runs or
production proof evidence. The actual observer rejected three incomplete-child
fixtures; the controller rejected three N24 launches lacking its required actual
owned cgroup. No large Final proof was rerun by those controls. No successful
production result is inferred from them.

The clean full1033-module route is separate from this resource continuation.
A source bundle must retain its own deterministic generation and actual fresh
verification commands; a continuation cannot be described as a monolithic
fresh run. No compiler correctness, entire ISO C semantics or hardware proof is
claimed by this numerical kernel-verification controller.
