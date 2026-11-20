/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import RamanujanPV.DemandCriticalPair.Final
import RamanujanPV.FirstCriticalCell
import RamanujanPV.RecoveredMargin
import RamanujanPV.LocalCells1000.Final
import RamanujanPV.QuotientDriverSuccess

/-! Closed source-first critical consumers. The actual two numerical count
proofs have completed their entire kernel pipeline and independent exact-query
and axiom audit. They instantiate the proved actual C counter execution model;
ordinary certificate evaluation is not being renamed program verification.
The complete finite interval through 1.49e12 is a separate, still open obligation. -/
namespace RamanujanPV.CriticalSourceClosed
open QuotientCCell FirstCriticalCell
set_option autoImplicit false

/-- An actual complete caller AST execution with its source-closed sqrt call. -/
theorem p_source : SourceExecution 38358837683 1644673232 :=
  QuotientCountRealization.source_execution_from_kernel_value (by norm_num) (by norm_num)
    DemandCriticalPair.pi_38358837683

/-- The second actual source execution is reused in every local consumer. -/
theorem q_source : SourceExecution 14111427770 632207037 :=
  QuotientCountRealization.source_execution_from_kernel_value (by norm_num) (by norm_num)
    DemandCriticalPair.pi_14111427770

theorem first_critical_interval {x : ℝ}
    (hx : (38358837683:ℝ) ≤ x) (hxNext : x < 38358837739) : Holds x :=
  conditional_first_critical_interval p_source q_source hx hxNext

theorem first_critical_margin {x : ℝ}
    (hx : (38358837683:ℝ) ≤ x) (hxNext : x < 38358837739) :
    (52869788:ℝ) < gap x :=
  RecoveredMargin.first_cell_margin_from_source p_source q_source hx hxNext

theorem preceding_counterexample : gap 38358837682 < 0 :=
  conditional_preceding_counterexample p_source q_source

/-- Eight checked adaptive cells, all newly encountered local primes proved by
Lucas certificates, cover every real point in this extended interval. -/
theorem first_1001_real_interval {x : ℝ}
    (hx : (38358837683:ℝ) ≤ x) (hxNext : x < 38358838684) : Holds x :=
  LocalCells1000.conditional_holds p_source q_source x hx hxNext

theorem preceding_failure : ¬Holds 38358837682 := by
  intro contrary
  have positive := (holds_iff_gap_pos _).mp contrary
  linarith [preceding_counterexample]

/-- Every successful complete driver execution emits the exact critical count,
under the explicitly specified little-endian word/stdio platform contract. -/
theorem successful_driver_bytes
    (layout : QuotientDriverInit.Layout) (token : Nat) (world : QuotientDriverExecution.World)
    {final : QuotientDriverExecution.DriverState}
    (run : QuotientDriverExecution.DriverRun token QuotientDriverSource.program.main.body
      (QuotientDriverExecution.initialDriver layout token world)
      (.returned final (.core (.i32 0)))) :
    final.world.buffered=[] ∧
      final.world.committed=world.committed++world.buffered++[208,184,7,98,0,0,0,0] := by
  have output := QuotientDriverSuccess.successful_main_output layout token world run
  change final.world.buffered=[] ∧
    final.world.committed=world.committed++world.buffered++
      QuotientDriverExecution.wordBytes (Nat.primeCounting 38358837683) at output
  rw [DemandCriticalPair.pi_38358837683] at output
  have encoded : QuotientDriverExecution.wordBytes 1644673232=[208,184,7,98,0,0,0,0] := by
    decide +kernel
  simpa only [encoded] using output

#print axioms p_source
#print axioms q_source
#print axioms first_critical_interval
#print axioms first_critical_margin
#print axioms preceding_counterexample
#print axioms first_1001_real_interval
#print axioms preceding_failure
#print axioms successful_driver_bytes
end RamanujanPV.CriticalSourceClosed
