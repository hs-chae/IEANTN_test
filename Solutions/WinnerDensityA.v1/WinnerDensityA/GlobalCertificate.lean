/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import WinnerDensityA.Program
import Lean
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace WinnerDensityA.GlobalCertificate
open Program WinnerProgramA
def bounds200 : List ℚ := [37/1000000000,16573281/1000000000]
theorem checked200 : acceptUpper (run (Program.program (1959/200) (893/200) 200 100 4096)) bounds200=true := by native_decide
theorem coefficient200 : rowCoefficient (fun _ ↦ (9.795:ℝ)) (fun _ ↦ (4.465:ℝ))
    (uniformGrid 4096) 4096 200 100 ≤ 16574/1000000 := by
  have h := source_linked_upper (Program.program (1959/200) (893/200) 200 100 4096)
    (run (Program.program (1959/200) (893/200) 200 100 4096)) bounds200 rfl checked200
  rw [program_semantics _ _ _ _ (by decide : 0<(4096:ℕ)) (by norm_num)] at h
  norm_num [bounds200] at h ⊢
  linarith
#print axioms coefficient200
def bounds300 : List ℚ := [2/1000000000,13105141/1000000000]
theorem checked300 : acceptUpper (run (Program.program (1959/200) (893/200) 300 100 4096)) bounds300=true := by native_decide
theorem coefficient300 : rowCoefficient (fun _ ↦ (9.795:ℝ)) (fun _ ↦ (4.465:ℝ))
    (uniformGrid 4096) 4096 300 100 ≤ 13106/1000000 := by
  have h := source_linked_upper (Program.program (1959/200) (893/200) 300 100 4096)
    (run (Program.program (1959/200) (893/200) 300 100 4096)) bounds300 rfl checked300
  rw [program_semantics _ _ _ _ (by decide : 0<(4096:ℕ)) (by norm_num)] at h
  norm_num [bounds300] at h ⊢
  linarith
#print axioms coefficient300
end WinnerDensityA.GlobalCertificate
