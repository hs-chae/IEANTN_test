/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import PVEvolutionA.Recovery.ProfileData
import PVEvolutionA.Recovery.ProfileFormula
namespace PVEvolutionA.Recovery.Profiles
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem arithmetic : ∀i : Fin 128,Profile.Arithmetic (row i) (slope i) := by native_decide

theorem scalar_checks : ∀i : Fin 128,Profile.ScalarChecks (row i) (slope i) := by native_decide

theorem shifts : ∀i : Fin 128,(row i).shift=(i.val:ℚ)/8 := by native_decide

theorem ordered : ∀i : Fin 127,
  (row ⟨i.val+1,by omega⟩).K≤(row ⟨i.val,by omega⟩).K ∧
  slope ⟨i.val,by omega⟩≤slope ⟨i.val+1,by omega⟩ := by native_decide

#print axioms arithmetic
#print axioms scalar_checks
#print axioms shifts
#print axioms ordered
end PVEvolutionA.Recovery.Profiles
