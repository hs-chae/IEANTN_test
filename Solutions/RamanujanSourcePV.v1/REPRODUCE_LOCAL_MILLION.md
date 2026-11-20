# Reproduce the recovered million-point Ramanujan interval

This procedure reconstructs the accepted base prime counts, local prime classifications, adaptive real cells, C-source proof consumers and strict margin from source. The numerical generators are untrusted. Their proposed outputs are accepted only after the relevant Lean kernel proofs and theorem-dependency checks succeed.

The selected result is unconditional Ramanujan positivity for every real x in [38,358,837,683, 38,359,837,684), with gap greater than 501,901. It includes the source-verified quotient-count outputs and an independently source-verified segmented checker for the local prime increments. This bounded interval does not complete the requested finite range through 1,490,000,000,000. The later source scalar/logarithm/checker overlay has its own reproduction stage and must not be inferred from this stage alone.

## Clean dependencies

Install exactly Lean 4.34.0-rc2 and the package revisions listed in BUILD_CONTEXT.json, including Mathlib 71a80585ee495fc24472fd0eaffc89d94e4fd8d6. Build those generic dependencies. Copy BUILD_CONTEXT.json to a clean-context JSON file and replace the compiler and generic-library/package paths with their actual clean-machine locations, preserving the listed commits and compiler SHA-256. Generic proof objects are reused; application proof objects are rebuilt in a new directory. The entry script checks the dependency commits and tracked-source cleanliness.

Use a Linux host with Python 3, a C++ compiler, GNU time, and the requested CPU IDs available. The pinned compiler must have SHA-256 e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550. The generators currently require Linux CPU IDs 4–7; the compiler CPU list is independently configurable. This is a resource/portability requirement of the recorded scripts, not a mathematical hypothesis. No random seeds are used.

## Full pipeline

Run from this directory, with a new output path whose parent exists:

```sh
bash scripts/reproduce_local_million_full.sh /absolute/clean-context.json /absolute/new-output 84,85,86,87,88,89 6
```

The script first generates the original 958 numerical-source files from the fixed query values and parameters, then checks every byte against evidence/LOCAL_MILLION_REPRODUCTION_IDENTITIES.json. It reconstructs the packed critical demand certificate, the 1,000-integer control, the 1,000,000-integer target window, the associated 367,880-integer quotient window, and all 285 adaptive real cells. It compiles the complete selected application closure in a fresh proof-object directory, including the actual C execution semantics and consumers. No original application .olean files are copied.

The source is staged in an isolated output checkout. The resource-only overlay installs the checked profiled replay controller and memory-profile JSON after the original deterministic source snapshot; RESOURCE_DRIVER_OVERLAY.json records both copies. No mathematical source is changed by this overlay.

The scheduler records each reserved memory cap before dispatch and never exceeds 300 GiB of combined reserved limits. The two known expensive critical checks receive 96 GiB each, the gap proof receives 192 GiB, and ordinary modules receive 48 GiB. It checks RAM independently of free disk space and preserves the configured host reserve. These are virtual-address-space ceilings, not actual measured RAM usage.

A completed generation can be resumed into its first fresh compilation run with:

```sh
bash scripts/reproduce_local_million_full.sh --prepared /absolute/prepared-output 84,85,86,87,88,89 6
```

This mode verifies the prepared source identities and refuses an already existing build output. It does not reuse an interrupted compiler run or its objects.

## Evidence and interpretation

Successful generation writes PREPARED.json and GENERATED_SOURCES.json. These prove deterministic regeneration only; they do not establish that Lean accepted the new replay. Successful full compilation writes build/RESULT.json with FRESH_SELECTED_SOURCE_CLOSURE_PASS and a final readback confirms CHECKED_COMPLETE_SELECTED_REPLAY. Inspect actual result files rather than treating a launched command as success.

Each compiler record preserves source snapshot/hash, exact command, compiler identity, stdout/stderr/rusage hashes, object hash, wall time, measured maximum RSS, resource cap and OOM/SIGKILL status. The final audit checks exact theorem types and permits only Lean's standard three logical axioms. Scheduler reservations are recorded separately from measured RSS; per-worker peak RSS must not be described as aggregate parallel peak RAM.

The source-counter proof is source-first PV. The Lucas/demand arithmetic certificates, dyadic e/log bounds, and row arithmetic are ordinary kernel verification supporting that source chain. The actual scalar-source overlay is a separate stage. Remaining generic trust includes the pinned Lean kernel/compiler/core runtime and the documented C integer/platform/runtime and hardware contracts; a source-to-AST proof does not itself verify the host C compiler's machine code.

The smoke mode of scripts/reproduce_local_million.py rebuilds only a small demand-count/cell/source-driver control and never claims the million result. Exact current-script positive runs were performed under normal Python, -O and -OO; their receipts are recorded in the research control ledger. The original full 958-source regeneration passed byte identity. The additional clean full theorem replay is recorded independently and may still be active; only its final RESULT establishes completion.

## Storage

Keep the source, exact input parameters, dependency pins, proof-source hashes, verification receipts and minimal regeneration identity files. Large generated arrays, proposal data, temporary build trees and caches may be removed only after the corresponding reproducibility result has been checked and their experiment-owned paths have been verified. Never remove original research sources or the sole accepted evidence copy. This entry script does not automatically delete data.
