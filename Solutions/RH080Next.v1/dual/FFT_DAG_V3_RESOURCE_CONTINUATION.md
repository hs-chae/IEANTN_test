# Resource-only continuation after an actual v2 failure

Leave an active compiler running. This additive fallback is for an actual failed
or interrupted v2 run; it is not authority to stop one that may finish.

The original experiment, source, checker, input, algorithm, 16,777,216-point grid,
rounding and target numerator remain unchanged. The v3 helper preserves the 992
original, four v1 and 35 v2 successful compiler receipts as distinct phases. It
accepts no failed or unreceipted Final output. The remaining Final and typed audit
are compiled from the same source with an initial 300 GiB virtual AS limit.
An unchanged independent 300 GiB physical cgroup/no-swap limit and host reserve
are still required. Virtual mappings are not physical RAM commitments.

```sh
python3 -u Solutions/RH080Next.v1/dual/resume_fft_dag_source_cold_v3.py \
  --context /path/to/pinned-context.json --candidate /path/to/fixed-candidate \
  --prefix /path/to/original-source-cold-run \
  --continuation /path/to/interrupted-v1-run \
  --nested-continuation /path/to/interrupted-v2-run \
  --run /fresh/v3-run --workers 12 --worker-memory-gib 300
```

The production resource command manifest records:

```json
{"phases":{"original_source_cold":992,"prior_continuation":4,
"prior_nested_continuation":35,"new_compilation":2}}
```

The independent `verify_fft_dag_nested_resume_v3.py` uses the v2 gate's options
(`--run`, `--context`, `--candidate`, `--output`, actual `--supervisor`,
`--command-plan`, `--stdout`, `--stderr`, `--unit`). It requires those exact phase
counts, the actual initial AS300 command and completed owned physical resource
evidence. `export_fft_dag_bank_v3.py` then exports accepted source/object/log/data
hardlinks with distinct per-module original compilation origins. Neither tool
calls this a monolithic fresh run or complete source-first PV.

Bounded actual controls under normal, `-O` and `-OO` include three successful
118-original/one-v1/one-v2 lineage checks, three newly compiled cheap typed audits
with initial AS300, three format exports and 24 tamper rejections. They do not
rerun the expensive Final module and do not claim production completion.

For a future clean run, `reproduce_fft_dag_bounded_v1.py` starts the unchanged
`reproduce_fft_dag_v2.py` under inherited AS300. Use its explicit arguments
`--context`, `--candidate`, `--run`, `--workers 12 --worker-memory-gib 300` inside
the owned supervisor. The corresponding independent gate and format adapter are
`verify_fft_dag_fresh_v2.py` and `export_fft_dag_fresh_bank_v2.py`. Their bounded
mathematical gate controls pass; the large clean workload has not been rerun.

`evidence/W4_N24_EXPECTED_INPUTS.json` preserves every original 1,033 source and
937 literal CSV identity, including the 1,020 generated module identities,
original input/producer/controller hashes and exact numerical parameters. New
deterministic generation must match every source/data hash; elapsed producer
time and the machine-absolute source-input location are not byte identities.
