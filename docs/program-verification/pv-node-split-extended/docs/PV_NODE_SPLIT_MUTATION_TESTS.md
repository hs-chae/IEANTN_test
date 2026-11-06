# Controlled mutation tests

Eleven kinds of change, each applied once in layout A (`pv8_wtA`) and once in layout B (`pv8_wtB`), plus a
compiler-flag experiment (MT7) that needs no Lean build and a configuration test of the freshness fix (R2).
Script `scripts/mutate.py`, driver `scripts/run_mutations.sh`, records `evidence/mutations/<id>_<worktree>/`
(`record.json` with every build log), digest `evidence/mutations/DIGEST.json`, table `scripts/mutation_table.py`.

## Protocol (every run)

1. Refuse to start unless the worktree's tracked files are clean; record the file's sha256 and `HEAD`.
2. Apply one edit (append or a unique replacement).
3. If a statement was edited: build the core, run `fingerprint --check` and `gen-challenges --check`, and grade
   an **in-memory** receipt for each layout conclusion with `assess` (recorded fingerprints = those committed at
   `HEAD` for the conclusion and its imports, as `record-receipt` writes them; current environment). No receipt
   file is written.
4. Build each layout project in order (guarded); record exit code, modules built, wall time, first error.
5. Query `solution_drift` with an in-memory receipt at `HEAD` for the layout's projects and for the projects that
   own the edited file, once with the repository's tool and once with the patched upstream tool (`pv8_wtU`).
6. Compare the edited file's sha256 with the local attestation that pins it (when there is one).
7. Restore the exact bytes; check sha256 equality and a clean `git status`; rebuild (the "restore" columns).

## Results

Layout projects: in A the one consumer (`A`; for MT11 the two consumers `A1`, `A2`); in B the provider (`P`) and the consumer (`C`); for MT11 B, `P` = `DudekPlattNumerics.v5` and `C` = `RamanujanGap.v3`. "ok / 8" = build succeeded, 8 modules rebuilt. Fingerprints and receipt grades are filled only for statement edits (MT4, MT5). Full table with drift wording, wall times and attestation pins: `evidence/mutations/TABLE.md`; raw records: `evidence/mutations/*/record.json`. In layout B the consumer is built after its provider, in the same worktree. All 22 runs restored the exact bytes and
left the tracked tree clean.

| Mutation (file) | Layout | Build after the edit: project rc / modules rebuilt | Restore | Fingerprints | In-memory receipt | `solution_drift`, node's project: current / patched |
|---|---|---|---|---|---|---|
| MT1 `qrh_trunc2.c` | A | A: ok / 8 | ok / 8, bytes identical, tree clean | n/a | n/a | A: none / reported |
| MT1 `qrh_trunc2.c` | B | P: ok / 8; C: ok / 0 | ok / 8; ok / 0, bytes identical, tree clean | n/a | n/a | P: none / reported; C: none / none |
| MT2 `qrh_trunc2.c` | A | A: FAIL / 5 (fails in `Table4Evolution.QRHTrunc`) | ok / 6, bytes identical, tree clean | n/a | n/a | A: none / reported |
| MT2 `qrh_trunc2.c` | B | P: FAIL / 5 (fails in `Table4Evolution.QRHTrunc`); C: ok / 0 | ok / 6; ok / 0, bytes identical, tree clean | n/a | n/a | P: none / reported; C: none / none |
| MT3 `qrh_trunc2.c` | A | A: FAIL / 5 (fails in `Table4Evolution.QRHTrunc`) | ok / 6, bytes identical, tree clean | n/a | n/a | A: none / reported |
| MT3 `qrh_trunc2.c` | B | P: FAIL / 5 (fails in `Table4Evolution.QRHTrunc`); C: ok / 0 | ok / 6; ok / 0, bytes identical, tree clean | n/a | n/a | P: none / reported; C: none / none |
| MT8 `Profiles.lean` | A | A: ok / 1 | ok / 1, bytes identical, tree clean | n/a | n/a | A: none / reported |
| MT8 `Profiles.lean` | B | P: ok / 1; C: ok / 0 | ok / 1; ok / 0, bytes identical, tree clean | n/a | n/a | P: none / reported; C: none / none |
| MT10 `ramanujan_9401_new.c` | A | A: ok / 0 | ok / 0, bytes identical, tree clean | n/a | n/a | A: none / reported |
| MT10 `ramanujan_9401_new.c` | B | P: ok / 0; C: ok / 0 | ok / 0; ok / 0, bytes identical, tree clean | n/a | n/a | P: none / reported; C: none / reported |
| MT10b `ramanujan_9401_new.c` | A | A: ok / 0 | ok / 0, bytes identical, tree clean | n/a | n/a | A: none / reported |
| MT10b `ramanujan_9401_new.c` | B | P: ok / 0; C: ok / 0 | ok / 0; ok / 0, bytes identical, tree clean | n/a | n/a | P: none / reported; C: none / reported |
| MT9 `NewA.lean` | A | A: FAIL / 1 (fails in `CalibrationPilot.NewChain`) | ok / 2, bytes identical, tree clean | n/a | n/a | A: none / reported |
| MT9 `NewA.lean` | B | P: FAIL / 1 (fails in `CalibrationPilot.NewChain`); C: FAIL / 0 (fails in `CalibrationPilot.NewChain`) | ok / 2; ok / 0, bytes identical, tree clean | n/a | n/a | P: none / reported; C: none / reported |
| MT11 `Applications.lean` | A | A1: ok / 1; A2: ok / 0 | ok / 1; ok / 0, bytes identical, tree clean | n/a | n/a | A1: none / reported; A2: none / reported |
| MT11 `Applications.lean` | B | P: ok / 1; C: ok / 0 | ok / 1; ok / 0, bytes identical, tree clean | n/a | n/a | P: none / reported; C: none / reported |
| MT6 `Solution.lean` | A | A: ok / 1 | ok / 1, bytes identical, tree clean | n/a | n/a | A: reported / reported |
| MT6 `Solution.lean` | B | P: ok / 1; C: ok / 0 | ok / 1; ok / 0, bytes identical, tree clean | n/a | n/a | P: reported / reported; C: none / none |
| MT4 `Conclusions.lean` | A | A: FAIL / 0 (fails in `RefinedConsumer`) | ok / 1, bytes identical, tree clean | moved: `QRHCH2.v5.psi_refined_bound` | A: BROKEN | A: none / none |
| MT4 `Conclusions.lean` | B | P: FAIL / 0 (fails in `RefinedConsumer`); C: ok / 0 | ok / 1; ok / 0, bytes identical, tree clean | moved: `QRHCH2.v5.psi_refined_bound` | P: BROKEN; C: green | P: none / none; C: none / none |
| MT5 `Conclusions.lean` | A | A: FAIL / 0 (fails in `Solution`) | ok / 1, bytes identical, tree clean | moved: `PVMatchT4A.v1.qrh_absolute_pi` | A: BROKEN | A: none / none |
| MT5 `Conclusions.lean` | B | P: FAIL / 0 (fails in `Solution`); C: FAIL / 0 (fails in `Solution`) | ok / 1; ok / 1, bytes identical, tree clean | moved: `PVMatchT4P.v1.qrh_pi` | P: BROKEN; C: BROKEN | P: none / none; C: none / none |

## Reading

**Sources edited in another solution project, declared to Lake (MT1–MT3, Table 4).** `Table4Evolution.v1` declares
`qrh_trunc2.c` as an input file, so every edit was seen. A trailing newline rebuilt 8 modules (169–178 s) and the
certificate still passed: the scanner compares tokens. A comment and a changed literal digit each rebuilt 5 modules
and then failed in `Table4Evolution.QRHTrunc` (`native_decide` evaluated the check to `false`). The rebuild is
coarse: `Partition`, `Bounds`, `Instance` and `Profiles` do not read the file and were rebuilt anyway. No
fingerprint moved; nothing mathematical changed. The local attestation's pin stopped matching, so the gate would
demand a new attestation. Layout B's consumer was never rebuilt, and it still built while its provider failed.

**Sources edited in another project, not declared (MT10, MT10b, the A→B′ pilot).** Nothing rebuilt in either layout
and every build succeeded, including after one digit of a program-B′ literal was changed: Lake replayed objects that
embed the old source. Only the attestation pin and the owning project's drift line noticed.

**A Lean file edited in another project (MT8, MT11).** A comment added to `Table4Evolution/Profiles.lean` or to
`QRHPropagation.v1/Applications.lean` rebuilt exactly that module; Lean's unchanged output stopped propagation. In
M3 the edited module lies in both layout-A consumers' closures and in neither layout-B consumer's.

**Proof route swapped, statement fixed (MT6).** Kernel-only route replaced by the native-assisted one: only
`Solution` rebuilt, no fingerprint moved, the drift line (own project) named `Solution.lean`; the proof gained one
native fact. No node or version is involved, as it should be.

**Program A's output weakened (MT9).** `NewA.bound` 457/5000 → 458/5000: the kernel-checked data link
`M = 120 + Δ` failed in `CalibrationPilot.NewChain` in layout A; in layout B the provider failed there, and the
consumer's own build (run second, in the same worktree) compiled the same module and failed with the same errors:
its solution imports `NewChain` (its static closure of 145 modules contains `CalibrationPilot.NewA` and `NewChain`),
although its proof never refers to program A.

**`solution_drift`.** With the repository's tool, the node's own project reported nothing in every cross-project
edit (MT1–MT3, MT8, MT9, MT10, MT10b, MT11: 20 queries of projects whose build reads the edited file), while the
owning project reported the change, worded
"no Lean source among them" for C files. With the patched tool the node's own project reported all 20, stayed silent for the five layout-B consumer
queries whose builds do not read the edited project, and also flagged `RamanujanGap.v3` in MT11, whose `Solution` does not import the edited module (package-level noise).

**An imported statement edited (MT4).** The ψ profile's constant `1/566` → `1/565` in
`QRHCH2.v5.psi_refined_bound`: the core rebuilt that node's `Conclusions` and the ten challenges that mention it
(13 s); `fingerprint --check` failed on that one conclusion only and advised a new version if it has dependants;
`gen-challenges --check` passed (challenge text names the import, so it does not change). In-memory receipts:
layout A's consumer BROKEN; layout B's provider BROKEN and its consumer **green**, since the consumer records
only its own and the provider's fingerprints. Both layouts' builds failed first in `QRHCH2.v5`'s own solution
module `RefinedConsumer`, which the Table 4 route imports; B's consumer built unchanged.

**The target constant edited (MT5).** `5·10⁻¹⁶` → `4.95·10⁻¹⁶` (still above the program's `4.930·10⁻¹⁶`) in the statement that carries it: layout A's consumer, layout B's provider. The edited conclusion's fingerprint moved and its in-memory receipt went BROKEN; the existing route proves `5·10⁻¹⁶`, so the solution failed. In layout B the consumer's own statement and fingerprint did not change, yet its receipt went BROKEN (it records the provider's fingerprint) and its proof failed too (the exact constant flows through `absolute_of_normalized`). A stronger target is a new statement in both layouts; B does not contain the change.

## MT7: compilers and flags (no Lean build)

Five selected C programs, seven flag sets each (`-O0`, `-O2`, `-O3 -march=native`, `-O3 -ffast-math`,
`-O2 -mfpmath=387`, `-O2 -mfpmath=387 -ffloat-store`, `-O0 -fexcess-precision=fast -mfpmath=387`), gcc 11.4.0:
identical binary64 results for four programs; program B′ (`ramanujan_9401_new.c`) under `-O2 -mfpmath=387` returns
`106.22239841212767` (`0x405a8e3bc68cb153`) instead of `106.22239841212769` (`…154`), one ulp lower
(`evidence/mt7_compiler/MT7_results.txt`). Nothing rebuilt and nothing went stale, because no Lake target, local
gate check or receipt field depends on a compiler or its flags. That is correct for what the proofs claim: they
are about the source under the modelled RN64 semantics, never about a compiled binary. It is also why "the C
program computes X" must not be written for a build with extended-precision intermediates.

## R2: does declaring the sources fix MT10b?

Yes. In layout A, `pilots/pv-replay/lakefile.toml` gained the two C files of programs A and B′ as `[[input_file]]`
entries and a library `PVReplayChainSources` with `roots = ["PVReplay.Chain"]` and `needs` on both (15 TOML lines,
`evidence/remedy/R2_run/lakefile.diff`; the same pattern `Table4Evolution.v1` uses). Script
`scripts/r2_input_file_test.sh`, logs `evidence/remedy/R2_run/`:

| Step | Build | Modules rebuilt |
|---|---|---|
| 1. sources declared | ok, 11 s | 1 (`PVReplay.Chain`, re-traced) |
| 2. declared, and MT10b's literal edit applied | **fails** in `PVReplay/Chain.lean:77` (`certificateB`: `native_decide` evaluated the check to `false`) | — |
| 3. edit reverted | ok | 1 |
| 4. declaration removed again | ok | 1 |

So the MT10b build that succeeded was replaying a certificate for bytes that no longer exist: a stale certificate, now
shown, not inferred. Declaring the sources turns it into a build failure. Tree clean after step 4.

## The provenance question

Can Lake, source hashes, local attestations, designated justifications, pinned solution projects and receipt
metadata together track these mutations? **Mostly yes, with two gaps, and neither gap depends on the layout.**

| Mutation class | What noticed it | Gap? |
|---|---|---|
| statement of the node edited (MT5) | `fingerprint --check` fails; an in-memory receipt grades BROKEN; the proof stops compiling | none |
| imported statement edited (MT4) | `fingerprint --check` names the moved import; a receipt of every conclusion importing it grades BROKEN, because receipts record the imports' fingerprints; Challenge files are unchanged | none |
| proof route swapped, statement fixed (MT6) | the solution's axioms (Comparator's check); drift of the node's own project | none |
| source of another project, declared to Lake (MT1–MT3) | Lake rebuilds and the certificate check fails where it should; the local gate's source pin | `solution_drift` of the consuming node's project is silent |
| Lean file of another project (MT8, MT11, MT9) | Lake rebuilds (or fails, MT9) | same drift gap |
| source of another project, **not** declared (MT10, MT10b) | only the gate's source pin and the owning project's drift line | Lake replays a stale certificate; drift silent |
| compiler or flags (MT7) | nothing, correctly: no proof depends on a binary | none for the claims as worded |

The **one sharply scoped tooling gap** is `solution_drift`'s scope: it diffs only the receipt's own project. The
failing example is any of 20 queries above (e.g. MT1 in layout A: `qrh_trunc2.c` edited, `PVMatchT4A.v1`'s drift
`None`), plus the unit test `test_a_program_edited_in_a_path_dependency_is_reported`. The smallest backward-compatible
fix is the 32-line patch (diff the in-repository path dependencies of the committed `lake-manifest.json`, leave out the
core); it reported all 20 and stayed silent where the solution does not depend on the edited project (the five
layout-B consumer queries), with one package-level false positive (`RamanujanGap.v3`, MT11). The **configuration
gap** is undeclared `include_str` sources (7 projects, 20 files): existing Lake facilities fix it (R2 above). No new
evidence graph, schema, receipt field or node is needed for either.
