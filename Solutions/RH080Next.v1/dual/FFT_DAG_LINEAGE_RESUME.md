# Continue the same interrupted FFT proof experiment

`resume_fft_dag_source_cold.py` continues the fixed W4 integer FFT certificate proof from a verified successful prefix of `reproduce_fft_dag_v2.py`. The original controller, candidate, input, numerical algorithms, grid, rounding, target numerator, mathematical checker and old outcome are preserved. This is kernel certificate verification; it becomes part of source-first PV only through the separately proved actual C caller and ANT consumers.

The resumed result is **source-cold lineage**, not a monolithic fresh build. Successful original modules are reused; only missing or unsuccessful modules are compiled. The final receipt states both counts. No unrelated application cache is searched or imported.

Before reusing anything, the controller checks the exact original driver and producer, candidate PLAN, pinned context/compiler/generic dependencies, every source/import identity, every literal input byte count/hash, and the independently specified typed claim. Every reused module must have a successful actual compiler receipt, the exact compiler/source command, matching source/object/stdout/stderr/time hashes, a completed GNU-time record, matching peak RSS and no strict compiler diagnostics. Its application dependencies must themselves belong to the verified prefix.

Sources, literal snapshots, accepted prefix objects and original successful receipts/logs are hardlinked into a fresh destination. A leftover object without a valid successful receipt is never linked or reused. The compiler receives only that destination object bank and the pinned generic libraries. The final fixed typed claim and all its axiom audits are the same as the original checker: execution trace, exact seed, complete twiddle recurrence, lengths, top shape, every stage decimation and the fixed original numerical result. The accepted axiom set is propext, Classical.choice and Quot.sound.

After independent resource admission, the production command is:

```sh
python3 Solutions/RH080Next.v1/dual/resume_fft_dag_source_cold.py \
  --context /data/ivy-rh-one-prime-20261124/clean_proof_context.json \
  --candidate /data/ivy-rh080-next-20261125/w4-dag24-candidate-v1 \
  --prefix /data/ivy-rh080-next-20261125/w4-dag24-kernel-parallel12-v1 \
  --run /data/ivy-rh080-next-20261125/w4-dag24-kernel-lineage-resume-v1 \
  --workers 12 --worker-memory-gib 256
```

Use an owned supervisor capped at300GiB aggregate RAM, no swap,256GiB host reserve and a290GiB total campaign scratch stop. The256GiB per-compiler limit is a VIRTUAL address-space limit: large shared imported proof-file mappings can exceed64GiB even when RSS is6–8GiB. It does not reserve256GiB of physical RAM per process, and its sum is not the aggregate RAM limit. The independent300GiB physical cgroup cap remains mandatory. RAM and free disk admission are separate. The controller does not fabricate OOM or aggregate peak-memory measurements; preserve the actual supervisor receipt. `--prepare-only` validates and hardlinks the lineage but runs no compiler and writes no acceptance.

For the interrupted N24 run, initial inspection found992 successful receipts out of1033 modules. The controller revalidates that count from actual files at launch and must compile the41 remaining modules. The old run remains interrupted by its scratch guard, return−15; completing the continuation does not rewrite that outcome.

## Checked bounded controls

`test_fft_dag_resume_bounded.py` uses an existing genuine13-stage source-cold fixture. Same-named modules remain unchanged. A genuine118-reused+2-fresh continuation, including the Final module and typed audit, completed first. Its unchanged2520-node quadrature fact costs several minutes, so the optimization controls reuse119 modules and actually compile the missing independent typed audit in normal, `-O` and `-OO` modes. All three pass the same18 exact claim/axiom roots.

Twenty-four actual negative CLI calls reject object mismatch, an exit0 PANIC, incorrect time/RSS evidence, altered compiler flags, a missing dependency receipt, a replaced fixed claim, an unknown compiler receipt and missing literal data. All original research files are unchanged. A redundant second full Final rebuild was stopped as test infrastructure, not a mathematical failure; its partial files and the executed harness are retained separately.

```sh
python3 Solutions/RH080Next.v1/dual/test_fft_dag_resume_bounded.py \
  --context /data/ivy-rh-one-prime-20261124/clean_proof_context.json \
  --candidate /data/ivy-rh080-next-20261125/w4-dag13-split-candidate-v1 \
  --cold /data/ivy-rh080-next-20261125/w4-dag13-typed-kernel-v1 \
  --out /fresh/bounded-resume-controls
```

The original clean reproduction route remains `reproduce_fft_dag_v2.py` on the immutable candidate and pinned generic context. Resume is an explicit efficiency option for an already verified prefix, never a substitute for that source lineage.
