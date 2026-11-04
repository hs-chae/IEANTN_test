# Solutions/RamanujanNumerics.v2: map from statement to program

This directory proves the updated numerical budget and holds the updated Ramanujan consumers. The
mathematics, in the order a reader should take it, is in
[docs/qrh/RAMANUJAN_WALKTHROUGH.md](../../docs/qrh/RAMANUJAN_WALKTHROUGH.md). This file only says
where each piece lives.

| You want | Look at |
|---|---|
| The public claim | `IEANTN/Nodes/RamanujanNumerics/v2/Conclusions.lean`: `epsilon_budget`, i.e. `εUpper(131,x) − εLower(119,e^3914,x) ≤ 9.101` for `x > e^3915` |
| The theorem that proves it | `Solution.lean`: `RamanujanNumerics.v2.challenge_epsilon_budget`, which uses `ForwardRamanujan.Updated.epsilon_bound` |
| The executed C | `c/updated.c`: `ramanujan_epsilon_bound`, seven literals, `*4096`, `-134`, `-119` |
| The instance certificate | `ForwardRamanujanUpdate/Updated.lean`: `source_check`, `enclosure_check`, `domain_check`, `execution_check`, `suffix_check`, `budget_check` (6 `native_decide`), then `concrete_execution`, `certified_upper`, `epsilon_bound` |
| Generic soundness (reused, frozen) | `../RamanujanNumerics.v1/ForwardRamanujan/Source.lean` (`Exec`, `source_linked_upper`) and `Math.lean` (`epsilon_majorant`, `gap_from_budget`, `loss_from_budget`) |
| Where the π input comes from | `ForwardRamanujanUpdate/Input.lean`: `supplied_pi` uses `DudekPlattNumerics.v5.challenge_pi_two_sided_qrh`, `pi_input` and `implies_old` |
| The Ramanujan consumers | `ForwardRamanujanUpdate/Consumer.lean` (`RamanujanGap.v2.challenge_*`). `Solutions/RamanujanGap.v2` only imports this file |
| Paired old+new assembly | `ForwardRamanujanUpdate/Assembly.lean`: `ForwardRamanujan.forward (hpsi : QRHCH2.v5.psi_refined_bound)` |
| Matched-target (grouped) controls | `Grouped.lean`, `OldGrouped.lean`, `UpdatedGrouped.lean`, and `c/oldgrouped.c`, `c/updatedgrouped.c` |
| Kernel-only source match | `ForwardRamanujanUpdate/KernelSource.lean`: `source_guard` (standard axioms only), `certified_upper` (5 native facts) |

Build: `lake update && lake build Solution ForwardRamanujanUpdate.Grouped ForwardRamanujanUpdate.KernelSource`
([REPRODUCING.md](../../docs/qrh/REPRODUCING.md) §3).

Trust:
- each budget certificate uses 6 finite `native_decide` facts, which is not official three-axiom
  compliance;
- the C semantics is the restricted RN64 model, and the compiler, runtime and hardware are trusted;
- `QRHCH2.v5.psi_refined_bound` is a hypothesis of `forward`.
