# Scoped Winner source-first PV: partial research checkpoint

**IN PROGRESS. This checkpoint does not complete the requested migration.**
The preserved original Scoped Winner final theorem has 49 native execution
dependencies; its joint before/after comparison consumes 50. A separate
intermediate overlay has recompiled all 106 consumers with 40 scalar facts
proved by the ordinary kernel: its actual remaining counts are 9 and 10. The
comparison-only theorem has zero in both versions. This kernel-only overlay
is **not source-first PV**. No official network evidence or assumptions change.

The immutable target is the original 39 comparator identities, 8,192 versus
16,384 integration cells, coefficients 0.009474458010474448 and
0.009471462010471452, and strict comparison for exp(330) ≤ x ≤ exp(331).
See the frozen identity and written-owner registries in `evidence/`.

Completed partial work in this checkpoint:

* Actual handwritten C++ evaluators reproduce all 52 rows underlying the 50
  joint numerical facts. They use the pinned generic Lean Nat object ABI,
  rather than calling a Lean evaluator or embedding computed answers.
* The 734-file C++ include bundle is associated compositionally with the full
  structured source AST. Lean proves every leaf binding, include-tree assembly,
  and exact functions/types/globals/input-array projections. The compiler and
  preprocessor remain explicitly trusted generic tools.
* The operational model includes checked C integers, records, pointers, arrays,
  explicit initialization and logical ownership. Source-body proofs currently
  cover 27 of the 68 original bodies, including comparisons, Nat wrappers,
  constructors, pool ownership and selected signed/rational/interval operations.
  The index names the exact contracts and remaining bodies; this is partial.
* Separate mathematical support proves Taylor/logarithm and
  prime-rich interval lemmas. The new fixed-point `basis_fp128.cpp` reproduces
  useful candidate quadratures; it is **not yet source verified**. The proved
  real interval model of its exponential routine is mathematical support only.

Still required: the remaining rational/interval/Taylor/DAG/quadrature C bodies;
complete numerical kernel certificates for the ten grid facts; unchanged Lean
consumer integration; separate final/comparison dependency audits; and a final
isolated source-cold verification. The analytic candidate near 0.00845 is not yet a completed numerical/source-PV
instance. Eight isolated exploratory exposure sessions have run: four original
pilot failures and four uniformly enlarged-budget followup successes. All four
followups were independently rebuilt. This is calibration evidence, not a
confirmatory or causal exposure claim.

`src/Checkpoint.lean` imports the accepted partial checkpoints. Its development
build and selected root axiom audits passed with only propext, Classical.choice
and Quot.sound. This used pinned development dependencies and is not a clean
final source-cold acceptance run. `MANIFEST.json` records exact source identities.
`STATUS.json` and `evidence/` keep numerical runs separate from formal proofs.

## Reproduction

Use Linux x86-64, Lean 4.34.0-rc2, Mathlib commit
71a80585ee495fc24472fd0eaffc89d94e4fd8d6, and the exact checkout containing
this directory. No numerical randomness is used.

```
python3 reproduce.py --check-local
python3 reproduce.py --lean-prefix /path/to/lean-4.34.0-rc2-linux --run-numerics --out /fresh/output
python3 reproduce.py --build-lean --out /another/fresh/output
```

The numerical command builds and executes the actual included program, checks
all 52 source-input bounds with exact rational arithmetic, and separately runs
the new basis scout. The Lean command asks Lake to resolve the existing pinned
path dependencies and build this partial checkpoint. Network access may be
needed for dependency/cache downloads. A full clean Lake reproduction is
**not yet executed for this checkpoint**; the saved development compile is
recorded accurately in `evidence/`. No final migration acceptance is implied.

The executable's generic Nat arithmetic, reference-count operations, Lean
initialization, precise compiler/ABI/runtime, standard I/O and hardware contracts
remain trusted. Application pool initialization, references, buffers and loops
must be proved applicable; output values or successful application execution
are never assumed platform facts. The new 512-bit backend has its own pending
source, overflow, buffer and whole-loop obligations.

The baseline source is commit 9f108629f0039584250b5e5d781f5313bb3d0ea8.
This is supplemental research, not a revision of locked historical outcomes.

The source include directory is `source/`, matching the exact `include_str`
paths in the Lean modules. A self-contained, actually replayed 142-module
source checkpoint is also supplied in `source-checkpoint-v2.tar.xz`; its README
describes generic dependency setup and the checked replay command. This remains
source-binding and raw-execution evidence, with application-body proofs pending.

## Supplemental checkpoint, 14 November

The exhaustive census covers 41 created declarations, both CLI routes and the
39 recorded comparator identities. Their required created/CLI native union is
51 (the selected joint union of 50 plus one sensitivity fact). The inherited
39-comparator proof union contains 78 native facts; 84 occur among all imported
native primitives. These populations are different; none is silently relabeled
as migrated. Exact written identities and use paths are preserved in the audit.

An additive C variant checks putchar/printf return values and flushes stdout
before success. It appends the four original sensitivity inputs to the original
52 rows. Lean has checked its 142-piece source AST, 728 unchanged copied-file
identities, and the four actual source-array-to-original-expression bindings.
Its full 56-row numerical replay passed in 1,320.80 seconds, with byte-identical original outputs and real /dev/full rejection. Whole arithmetic,
loop, initialization, stream-effect and theorem-provider proofs remain open.

The new 512-bit basis backend has actual source-body proofs for addU, mulU and
zero, including the multiplication guard and zero short circuit. Its source
initialization is proved from the actual bound global declarations. The complete
19-function backend remains unfinished. Positive exp/log/interval models are
mathematical support and do not substitute for its source-body proofs.

The standalone source-binding capsule was actually replayed from 142 fresh
application source modules with public generic dependencies and all 52 actual
C rows; it reused no old application objects. This was a host source-cold run,
not a namespace-isolated final migration run. The additive runtime guard was
tested separately and is not mislabeled as a second complete replay.

The offline [analytic research progress report](ANALYTIC_RESEARCH_PROGRESS.html)
records 20 mechanisms, mathematical partial proofs, numerical scouts and serious
challengers. It is a checkpoint, not the final project report or a claim that
the remaining numerical/source-PV instances are complete.

`c56-and-rational-source-checkpoint-v1.tar.xz` preserves the additive C56
source, its actual AST/input proofs, accepted rational helper sources (including
qm), scripts, receipts and source hashes. Its numerical runner accepts explicit
source/toolchain/reference-output paths. The combined clean source-cold replay
was not completed before the usage stop; no full source-PV claim is made.

The final saved mathematical result is unconditional:
`SynergyAnalytic.tangent256_universal_basis_caps` proves the three true
Gaussian basis caps (1.865, 0.6365, 0.516) using genuine 272-cell ordinary-kernel
execution, real soundness and analytic tails, with only standard Lean axioms.
`J_CAPS_SOURCE_CHECKPOINT_V1.zip` preserves its 96-source dependency closure,
receipts and README. This is kernel-only verification, not C-source PV. The
new height/PNT numerical instance remains unfinished.

`SCOPED_16_BODY_SOURCE_COLD_COMPONENT_V1.zip` contains the independently
replayed 16-body/46-source component and reproducible scripts (302.90 seconds).
It is host source-cold, not final namespace isolation. The later merged28-body
and C56 source-cold replay remains pending.

## Continued source proofs and fresh replays

Two additive source-cold components are available:

* `SCOPED28_C56_SOURCE_COLD_COMPONENT_V3.zip`:343fresh application sources,885exact include payloads,60Std3root audits,28actual old-C body contracts and the checkedC56 source/auxiliary bindings,1571.56seconds.
* `POSITIVE6_STDIO_SOURCE_COLD_V1.zip`:52fresh application sources,53payloads,24Std3root audits,238.34seconds. Covers six actual C512 arithmetic bodies and the additive StdIO model/actual checked-flush statement. The later seventh body, positiveSub, and its mathematical join are explicitly a host-only supplement.

Both runs start with empty application object directories and use only pinned public generic dependencies. Both are HOST runs, not namespace isolation or repeat numerical C executions. Each archive includes clean setup/reproduction scripts, source hashes, accepted receipts and actual root-audit logs. Source-first verification of the complete numerical applications and final ANT providers remains unfinished.

The StdIO model allows failures and partial writes, and proves delivery from a zero fflush return. Its actual source-branch theorem is conditional in an arbitrary failure policy; it does not assert all application writes succeed or that the emitted mathematics is correct. Printing, buffers/lifetimes, complete main correctness and theorem consumption remain mandatory.

`BODY32_SOURCE_SUPPLEMENT_V1.zip` records32 actual original C body contracts
with the corresponding mathematical joins, including signed/rational
comparison and rational min/max. Its119-source/47-root clean-replay recipe is
preserved, but this combined32-body cold replay has not been executed; its
proof receipts are source-associated host builds. The earlier28-body cold
replay remains separate accepted evidence.
