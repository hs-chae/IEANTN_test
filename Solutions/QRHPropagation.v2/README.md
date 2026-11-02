# Targeted QRH propagation, Phase2

Run `lake build Phase2Solution Phase2Replay ComparisonsPhase2` in this directory,
with Lean4.34.0-rc2 and the committed dependency pins. The other nine new family
solution packages import this shared implementation through a local dependency.
`comparator.json` in each package names only that node's exact generated challenges.

The core statement files are immutable new versions. Existing conclusion and
fingerprint files are unchanged. Generated Challenge placeholders are intentional;
proof modules do not import them. Official verification receipts remain pending.

`Polynomial` retains the paired CH2 zero-count polynomial and uses the original
thirteen analytic inputs. All density consumers additionally use the corrected
FKS density and finite-height RH inputs via QRHCH2.v2. `Phase2Replay` composes these
proofs with QRH and the existing proved prime-interval and Dudek-Platt criteria;
no new transfer or arithmetic criterion is assumed.

`Frontier`, `PartialSummation`, `IntervalsSharp`, `FKSQuantitative`,
`RemaindersPhase2`, `RamanujanPhase2`, `TablesPhase2` and `ArithmeticPhase2`
contain the substantive proofs. `ComparisonsPhase2` certifies the selected
whole-ray comparisons and retains the Phase1 pi expansion where it is tighter.
The classical hybrid contracts preserve their old small-x estimates exactly.

The separate actual OpenAI QRH replay uses its own Lean4.34.1 environment;
no compiled proof is imported across compiler versions. Literature-backed
analytic and finite computation premises remain explicit in both environments.
No best-known or optimality claim is made.
