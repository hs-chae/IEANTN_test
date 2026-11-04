/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import WinnerDensityA.ModelProgram
import Lean
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace WinnerDensityA.ModelCertificate
open Program ModelProgram WinnerProgramA
def bounds200 : List ℚ := [31/1000000000,12597192/1000000000]
theorem checked200 : acceptUpper (run (ModelProgram.program (39/5) (53/10) 6 200 100 4096)) bounds200=true := by native_decide
theorem coefficient200 : rowCoefficient (ModelProgram.modelC (39/5) (53/10)) (fun _ ↦ 6)
    (uniformGrid 4096) 4096 200 100 ≤ 12599/1000000 := by
  have h := source_linked_upper (ModelProgram.program (39/5) (53/10) 6 200 100 4096)
    (run (ModelProgram.program (39/5) (53/10) 6 200 100 4096)) bounds200 rfl checked200
  rw [ModelProgram.program_semantics _ _ _ _ _ (by decide : 0<(4096:ℕ)) (by norm_num)] at h
  norm_num [bounds200] at h ⊢
  linarith
#print axioms coefficient200
def bounds300 : List ℚ := [2/1000000000,10180130/1000000000]
theorem checked300 : acceptUpper (run (ModelProgram.program (39/5) (53/10) 6 300 100 4096)) bounds300=true := by native_decide
theorem coefficient300 : rowCoefficient (ModelProgram.modelC (39/5) (53/10)) (fun _ ↦ 6)
    (uniformGrid 4096) 4096 300 100 ≤ 10182/1000000 := by
  have h := source_linked_upper (ModelProgram.program (39/5) (53/10) 6 300 100 4096)
    (run (ModelProgram.program (39/5) (53/10) 6 300 100 4096)) bounds300 rfl checked300
  rw [ModelProgram.program_semantics _ _ _ _ _ (by decide : 0<(4096:ℕ)) (by norm_num)] at h
  norm_num [bounds300] at h ⊢
  linarith
#print axioms coefficient300
end WinnerDensityA.ModelCertificate
