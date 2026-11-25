# Reproduction portability review

This bounded read-only review covers the study wrapper, its input inventory and
documentation, the clean-root exposure adapters, and the newly added compact
source bootstrap. Exact accepted file identities and check receipts are recorded
in `REVIEW.json`. This review does not rerun heavy Lean proofs or model trials.

The 278-file mathematical inventory covers all eight default profiles and their
207 distinct Lean source files. Including the two optional scalar profiles gives
209 distinct Lean files. The compact export additionally needs
`materialize_generated.py` and `GENERATED_CELL_SOURCES.json`: they restore exactly
25 G80 and 24 G56 cell files before the ordinary 278-file checks. Source
materialization is explicitly separate from Lean acceptance.

Two concrete problems were repaired. The original G80 controls unconditionally
read a historical private cell bank, and several G80/G56 child controls omitted
the supplied context. The repaired controls derive their negative fixture from
the supplied fresh accepted run and pass the explicit context and repository
LeanCert source to every child. Their actual 20 and 14 cases passed. The wrapper
also now emits `PASS_STUDY_REPLAY_CONTROLS_OMITTED` when controls are skipped,
reserving the full checked status for the complete selected procedure.

The optional scopes are stated separately: 353 predecessor proof modules,
original source-supplement/Arb computations, optimizer rediscovery, model trials,
and ordinary Lake packaging. Paper/corpus bytes, exact generic infrastructure,
model/account requirements and host-mapped Lake metadata are not silently
included in the mandatory mathematical inventory. Historical absolute paths in
receipts and inactive defaults are provenance; the mandatory child commands use
explicit current inputs. Model outputs have no promised byte-identical replay.

The available execution evidence includes deterministic source regeneration,
relocated scalar Lean execution, optimization-mode CLI controls, and separate
NOAUTH namespace/proof-import fixtures. The compact bootstrap actually restored
all 49 omitted sources and passed all 278 hash guards. These bounded executions
do not constitute a newly executed all-lane proof run under the revised wrapper.
The separate accepted cold mathematical replays retain their own source and
execution identities. Only the actual C-to-consumer route is source-first PV;
the Gaussian and other numerical proofs remain kernel mathematics.
