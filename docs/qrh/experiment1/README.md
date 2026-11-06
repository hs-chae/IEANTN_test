# Experiment 1: frozen evidence versus verified program evolution

This is the publication of the completed historical study on `experiment/e1-frozen-evidence`.
Start with this guide and [the rendered mathematical report](E1_FINAL_REPORT.html).
Download that HTML file and open it to read the equations offline; its math font is embedded.
[The exact comparison table](E1_COMPARISON.csv) records full functions and real domains.

The outcome is mixed. Three conditional, native-assisted Lean conclusions—psi error,
the weighted von Mangoldt sum and normalized prime-counting error—have a proved strict
advantage against the complete final frozen-evidence baseline on the closed comparison domain.
Their validity is proved on full rays. The analytic baseline proves a smaller prime interval
than the evolved program. The unchanged-program V phase has zero mathematical-strength gain.
No optimality, global best-known result, universal PV necessity or automatic official-graph update
is claimed. The report renders the exact bounds, common hypotheses and thresholds.

## Source entrypoints

| Purpose | Source |
|---|---|
| Matched common-premise consumers and comparisons | [E1Comparison/Matched.lean](../../../Solutions/E1Comparison.v1/E1Comparison/Matched.lean) |
| Cumulative treatment preserving every baseline improvement | [E1Comparison/Cumulative.lean](../../../Solutions/E1Comparison.v1/E1Comparison/Cumulative.lean) |
| Every-positive-grid comparison, with exact continuous integration | [E1Comparison/AllGridFloor.lean](../../../Solutions/E1Comparison.v1/E1Comparison/AllGridFloor.lean) |
| Actual OpenAI QRH bridge | [IEANTNQRHBridge.lean](../../../Solutions/OpenAIQRH.v1/Actual/IEANTNQRHBridge.lean) |
| Actual-QRH matched common-premise comparisons | [E1MatchedActual.lean](../../../Solutions/E1Comparison.v1/Actual/E1MatchedActual.lean) |
| Actual-QRH prime consumers | [E1NPlusActual.lean](../../../Solutions/E1NPlus.v1/Actual/E1NPlusActual.lean) |
| Actual-QRH cumulative consumers | [E1FinalActual.lean](../../../Solutions/E1NPlus.v1/Actual/E1FinalActual.lean) |
| Final paired baseline, including symbolic-grid infima | [E1NPlus/TightAll.lean](../../../Solutions/E1NPlus.v1/E1NPlus/TightAll.lean) |
| Final prime-counting baseline | [E1NPlus/AbsoluteFinal.lean](../../../Solutions/E1NPlus.v1/E1NPlus/AbsoluteFinal.lean) |
| Analytic prime-interval attack and real-ray consumers | [E1NPlus/Result.lean](../../../Solutions/E1NPlus.v1/E1NPlus/Result.lean) |
| Supply the old Ramanujan consumer's PNT premise | [E1NPlus/Downstream.lean](../../../Solutions/E1NPlus.v1/E1NPlus/Downstream.lean) |
| Evolved short-interval numerical chain | [HighAnchorIntervalB/Result.lean](../../../Solutions/HighAnchorIntervalB.v1/HighAnchorIntervalB/Result.lean) |
| Evolved weighted/psi coefficient | [LambdaEvolutionA/WithoutCotangent.lean](../../../Solutions/LambdaEvolutionA.v1/LambdaEvolutionA/WithoutCotangent.lean) |
| Selected evolved prime-counting result | [Recovery/MixedProof.lean](../../../Solutions/PVEvolutionA.v1/PVEvolutionA/Recovery/MixedProof.lean) |

The common source contracts remain explicit hypotheses. Finite RH is only up to the stated
verified height. The actual pinned OpenAI QRH theorem was supplied in the compatible replay;
it was not replaced by an assumed final estimate. The full consumers use native facts and are
not standard-axiom-only. The generic analytic comparison lemmas use the standard three axioms.

## Chronology and evidence

The historical starting snapshot is `00128bef2f361e9f56795ddd4bb0cf0753643b81`, after the
already-published `e0c1cebf` work and before the later No-PV/recovery experiments. The same
researcher completed N, V, E and Nplus sequentially, sealing each stage before continuing.
Independent final readers were used only after the research. This is retrospective, informed
and not blinded or preregistered. It is not a causal test of structural exposure.

The original census has114 versions,58families and243rows including3empty stubs. The23,122-row
frozen inventory is a declaration/table candidate census, not an exhaustive checked source-claim
universe. All legacy numerical facts were retained regardless of verification tier. Full inventory
and immutable N/V/E/Nplus archives are separately delivered; [ARTIFACTS.json](ARTIFACTS.json)
records filenames, sizes and hashes without publishing private delivery links.

Read [the final challenge](E1_PHASE4_ADVERSARIAL_NOPV.md),
[program lineage](E1_PROGRAM_LINEAGE.csv), [revert evidence](E1_REVERT_TESTS.md),
[search ledger](E1_NPLUS_SEARCH_LEDGER.csv), and the three final reviews:
[mathematics](evidence/FINAL_MATH_AUDIT.md),
[fidelity](evidence/FINAL_FIDELITY_AUDIT.md),
[evidence](evidence/FINAL_EVIDENCE_AUDIT.md).
The corrected C locator/FKS-premise erratum and fresh actual-prime-wrapper binding supplement
are preserved in the evidence subdirectory. Neither changed a mathematical statement or output.
These are nonofficial research records; no official receipt or designation was written.

## Replaying the proofs

Canonical: Lean4.34.0-rc2 / Mathlib71a80585ee495fc24472fd0eaffc89d94e4fd8d6.
Actual OpenAI: Lean4.34.1 / Mathlibd13f23b723b8a846827a245b89c10fc7d3f11612.
Keep the object environments separate. OpenAI source is pinned at
`openai/math@7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a`.

These new families are experimental solution libraries, outside the default core build.
**Ordinary `lake build` does not check this experiment.** No untested Lake configuration was
added for publication. The recorded bounded Lean-driver replays use explicit project roots and
matching compiled dependency paths. [REPRODUCING_EXPERIMENT1.md](REPRODUCING_EXPERIMENT1.md)
records commands that actually ran in the original workspace and distinguishes fresh modules
from byte-matched cache reuse. Original run paths in research records are provenance, not a
promise that those paths exist on a clean checkout. A full clean-cache build was not performed.
The delivered source/verification-tool companions contain the exact replay drivers and inputs.

Fresh method controls total530 across all five Python modes;170 historical method controls
are explicitly reused. The native method requires both a passed status and the program-verified
method tag. Final byte-manifest controls do not establish mathematical validity.
The separate verifier companion includes1073hash-matched files. The historical forward
all-route cold replay deliberately omits a private implementation prompt and a larger unsnapshotted
artifact closure; validators were not weakened. This administrative replay limit is not an
additional premise of the completed mathematical theorems.

## Publication scope

This branch adds183reviewed mathematical library sources, four actual-QRH replay entrypoints and this documentation. Six source
headers were normalized with identical mathematical bodies and11fresh module replays; two
side-effectful historical audit drivers stay outside the mathematical library. All2080files in
the historical starting tree are unchanged. Core definitions, nodes, fingerprints, policies,
official receipts and generated views are unchanged. Research reports' historical no-push
statements describe their earlier checkpoints; this is a separately authorized publication.
The existing owner `qrh-2pv` and all other remote branches are preserved.

Unrelated earlier general-beta/global/literature formalization tasks remain outside this
completed conditional study. No official graph registration, PR or verification dispatch was
performed as part of this publication.

Publication smoke checks freshly replayed the canonical prime/Matched roots and the four actual-QRH entrypoints from this checkout under their separate pins; no expensive numerical provider was re-executed. The actual bridge receives a copyright header only; its mathematical body is identical to the previously audited source.

Publication checks:311unit tests pass and six source-root replays pass. The repository-wide metadata check still reports49 inherited fork-receipt provenance findings; its output is byte-identical to the clean00128baseline. No receipt or validator was changed to suppress them. See [PUBLICATION_CHECKS.json](PUBLICATION_CHECKS.json), [SOURCE_MAP.json](SOURCE_MAP.json) and [REPORT_PORT.json](REPORT_PORT.json).
