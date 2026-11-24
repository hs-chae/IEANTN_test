# Actual high-input main and its application proof

The additional C main calls the unchanged `rpc_quotient_count` implementation at
`1490000000000`, with capacity `1500000` in each static array. The original main
at `38358837683` and its source files are preserved. The added C file changes
that input literal only. It writes an eight-byte result and checks both `fwrite`
and `fflush` failure branches.

`HighDriverSource.lean` proves exact rendered source bytes and the existing
restricted `SourceCorresponds` predicate. `HighDriverRuntime.lean` reuses the
original execution semantics and proves the actual source globals' initialization,
typed counter call, local result-object allocation and lifetime, possible full
main execution, and correctness of every successful main execution.
`HighDriverContract.actual_source_model_main` supplies all those obligations with
no arguments. `complete_canonical_model_run` constructs an inhabited concrete
layout and full successful model run. The resulting mathematical output is
`Nat.primeCounting 1490000000000`; its numerical evaluation is a separate gate.

From the network root, after installing the pinned Lean/mathlib context:

```sh
python3 Solutions/RHOcticPush.v1/ramanujan/count-feasibility/high-driver/reproduce_application.py \
  --out /absolute/fresh/application-proof
python3 Solutions/RHOcticPush.v1/ramanujan/count-feasibility/high-driver/reproduce_application.py \
  --verify /absolute/fresh/application-proof
python3 Solutions/RHOcticPush.v1/ramanujan/count-feasibility/high-driver/run_native_high.py \
  --out /absolute/fresh/native-high --cpu 86
```

The first command reconstructs the complete application import DAG from the
preserved small source pack and the six high-main proof modules, compiles it
without historical application objects, runs a complete theorem axiom audit,
and checks actual import probes. It uses one compiler at a time with a 64GiB
address-space cap and separately checks the 512GiB host reserve. Generic library
objects and the exact pinned compiler remain trusted infrastructure. Adjust
`--context` for a clean machine's paths while retaining the recorded compiler
hash and dependency revisions. `run_native_high.py` uses ordinary C compilation
and records exact source/compiler/executable/output hashes and measured time/RAM.
Choose any available CPU through `--cpu`.

The recorded native run emitted `55206486339` in 1.116 seconds with 20,420KiB peak
RSS. This observation alone is not a Lean theorem evaluating the prime count.
The separate complete 90,670,946-record kernel campaign, unchanged Final, source
function consumer, and complete axiom audit must finish before instantiating the
exact output adapter. `HighDriverFinal.lean.in` records that pending adapter; it
is not a compiled proof artifact. No cardinality of finished certificate nodes
or finite Ramanujan prefix coverage is inferred from exploratory Python counts.

The source correspondence here is the old rendered-byte/token backend. An
independent C parsing/renderer soundness theorem is still missing. Interpretation
of the C AST execution model and the precise compiler, ABI, runtime, stdio, OS,
and hardware contracts remain explicit boundaries. This directory does not
claim complete source-first PV. The fresh kernel application proof, the separate
kernel numerical certificate, and ordinary native execution are distinct results.

`SOURCE_FREEZE.json` pins the actual six Lean modules, unchanged counter and new
main, development receipts, and native execution receipt. Original failed or
superseded development attempts are retained in the parent attempt ledger.
