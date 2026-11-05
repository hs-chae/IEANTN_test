/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import WinnerProgramA.Program
import Lean
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace WinnerProgramA
def p0_lo : List ℚ := [0/1000000000, 7/1000000000, 76/1000000000, 664/1000000000, 5763/1000000000, 50059/1000000000, 435873/1000000000, 3803549/1000000000, 8561781/1000000000, -1/1000000000]
def p0_hi : List ℚ := [3/1000000000, 10/1000000000, 79/1000000000, 667/1000000000, 5766/1000000000, 50062/1000000000, 435876/1000000000, 3803552/1000000000, 8561784/1000000000, 2/1000000000]
def p1_lo : List ℚ := [0/1000000000, 7/1000000000, 75/1000000000, 663/1000000000, 5751/1000000000, 49962/1000000000, 435029/1000000000, 3796181/1000000000, 8545202/1000000000, -1/1000000000]
def p1_hi : List ℚ := [3/1000000000, 10/1000000000, 78/1000000000, 666/1000000000, 5754/1000000000, 49965/1000000000, 435032/1000000000, 3796184/1000000000, 8545205/1000000000, 2/1000000000]

theorem p0_execution : Exec p0 (run p0) := rfl
theorem p1_execution : Exec p1 (run p1) := rfl
/-- Finite native computation of the actual interval program, not an analytic oracle. -/
theorem p1_check : acceptUpper (run p1) p1_hi = true := by native_decide
theorem p0_check : acceptLower (run p0) p0_lo = true := by native_decide

theorem p1_upper : value p1 ≤ (12833/1000000 : ℝ) := by
  have h := source_linked_upper p1 (run p1) p1_hi p1_execution p1_check
  norm_num [p1_hi, List.sum_cons] at h ⊢
  linarith

theorem p0_lower : (128577/10000000 : ℝ) ≤ value p0 := by
  have h := source_linked_lower p0 (run p0) p0_lo p0_execution p0_check
  norm_num [p0_lo, List.sum_cons] at h ⊢
  linarith

/-- Strict improvement of the computed finite expressions only; no PNT bridge claimed. -/
theorem expression_improvement : value p1 < value p0 := by
  have hn := p1_upper
  have ho := p0_lower
  linarith
#print axioms p1_upper
#print axioms p0_lower
#print axioms expression_improvement
set_option pp.proofs false in
#print expression_improvement
end WinnerProgramA
