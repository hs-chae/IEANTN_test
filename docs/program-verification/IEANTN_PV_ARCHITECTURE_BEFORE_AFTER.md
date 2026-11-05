# Program verification in IEANTN: architecture before and after

## 1. What did not change

- **The architecture.** Node statements, imports, generated challenges and per-node solution
  projects were not touched. The node graph still records only mathematical propositions.
- **Official state.** No `kind`, `designated` value, receipt or frozen file changed. `check` still
  fails on exactly the 49 inherited receipt-provenance items.
- **Why the existing interfaces suffice.** A solution project may require other solution projects
  by path. Table 4 already reused `SumStability` that way. The upgrade uses this mechanism and adds
  no new kind of dependency.

## 2. Map

```
BEFORE                                             AFTER
Solutions/FKS2Numerics.v2  SumStability (loop)     Solutions/FKS2Numerics.v2  SumStability (unchanged)
Solutions/FKS2Numerics.v5  FKS2Table4: own         Solutions/ProgramVerification   (new, shared)
     program shape, Exec, chain/suffix proofs           PVCore: one program shape, Exec, error
Solutions/FKS2Numerics.v6  FKS2Pair: again              theorems, certificate + soundness, bridges
     Exec, sum_upper, source_linked_upper               PVRamanujan.Family: the budget family theorem
Solutions/RamanujanNumerics.v1  ForwardRamanujan:   Solutions/RamanujanNumerics.v3  (new provider)
     own shape, Exec, scanner, glue                     generated: C file + 26-line data module
  + 4 instance files × 116 lines (6 native each)   Solutions/RamanujanGap.v3  (new consumer)
pilots/agentB-calibration  NamedSource + 4         pilots/pv-replay  (research)
     instance files                                      v1, v2, grouped, Table 4 old/QRH and the
                                                         A→B′ chain, re-derived on PVCore
```

## 3. The bottlenecks that mattered, measured

| Bottleneck | Before | After |
|---|---|---|
| Per-instance proof glue | 18 theorems, 116 code lines, 6 native facts per Ramanujan instance | 2 theorems, 10–13 lines, 1 native fact (4 replays); 26 lines for the new generated provider |
| Copies of the execution infrastructure | `loadLiteral`, `runSum`, `chainCheck`, `chain_sound`: 2 copies; `kernel_from_chain`, `output_unique`, `sum_upper`: 2–3 copies | 1 copy each, in `PVCore` |
| Native facts in the A→B′ chain theorem | 13 | 2 |
| Native facts per Table 4 instance | 8 | 4: 3 analytic enclosure facts kept, plus 1 certificate |
| A changed C file | replayed stale by Lake; found only by the gate's hash check | rebuilt (`input_file` + `needs`); the certificate then fails (controls A, B) |
| Steps for a changed provider | copy a file, regenerate data, rename, re-prove | register the change, `pv_update.py generate`, build, gate (`IEANTN_PV_UPDATE_WORKFLOW.md`) |
| Program evidence on the node page | method, gate, kind, receipt | plus the selected file and its hash, the proving theorems, trust in plain words, other checked routes, and the registered change |

The shared code was 382 lines at the end of round 1, written once: PVCore 335 and the Ramanujan
family 47; after the second round it is 702 (PVCore 614, family 88). Code lines; round 1 from
`census_after.json`, round 2 counted the same way.

**Unit of measurement.** All line counts are code lines: blank lines, comments and docstrings
excluded.

**What was not measured.**
- Contributor time.
- Build time for a cold Mathlib; all builds reuse the pinned cache.

## 4. Why a minimal evolution, and where it stops

- **Solution-facing, not core.** The shared package is not in the core build and not visible to
  statements, so `check-closure` and fingerprints are unaffected.
- **Few requirements.** Its requirements are kept to the stable packages its contracts stand on.
  Every requirement there enters every provider's manifest. This was learned when adding the pilot
  there made a provider's manifest stale.
- **One program shape.** It is the shape all existing executed providers have. No general C
  frontend was built.
- **One family adapter, Ramanujan.** Table 4 uses the generic bridge, because its numerical
  obligation is a single inequality that its analytic enclosures already prove.
- **Not done.**
  - A weighted sum with per-entry scales: no current application uses one.
  - Inputs outside `[2⁻⁴⁰, 1]` per entry: the generator scales them in; the loop bound is
    unchanged.

## 5. Second round (2026-11-05): what was added after the first report

| Item | Where | Result |
|---|---|---|
| Sums of more than 64 entries | `PVCore.Chunked` | one frozen `sum` call per chunk of ≤ 64, wrapper additions certified; Table 4 in 2 chunks and a 100-entry test |
| Fewer trusted computations | `PVCore.Kernel`, `PVRamanujan.Kernel` | native fact = literal decoding only; the A→B′ chain on 2 decoding facts (KernelB) |
| A second backend | gate `backends`, `lean-dyadic-expr` | Agent A's generated-expression provider passes the gate (49 native facts) |
| Two-backend composition | `pilots/pv-twobackend` | Agent A's π bound → kernel-checked link → C budget program; 50 native facts |
| π premise of `RamanujanGap.v3` | replay | discharged by `DudekPlattNumerics.v5`'s solution; std + 1 native |
| Freshness on published providers | lakefiles of `RamanujanNumerics.v2`, `FKS2Numerics.v5` (covers `v7`) | `input_file` + `needs`; controls in `PV_TEST_AND_REPLAY_LOG.md` |
| Page generator | `scripts/ieantn.py` | node README link; "Local proof" row; `IEANTN_REPOSITORY_URL`/`_BRANCH` |

```
AFTER, second round (additions)
Solutions/ProgramVerification   + PVCore.Kernel, PVCore.Chunked, PVRamanujan.Kernel, budget_shift
pilots/pv-replay                + KernelChain (KernelB), Chunked (Table 4 in chunks, 100 entries)
pilots/pv-twobackend            (new) Agent A's dyadic provider → data link → C budget program
scripts/native_assisted         gate: per-endpoint backends (restricted-c-binary64, lean-dyadic-expr)
```
