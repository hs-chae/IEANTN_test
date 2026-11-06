/- Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import PVEvolutionA.Recovery.MixedProgram
namespace PVEvolutionA.Recovery.Mixed
set_option maxHeartbeats 0
 theorem cases_of_checks
    (h0 : Chunks.baseAccepted && Chunks.accepted 0=true)
    (h1 : Chunks.accepted 1=true) (h2 : Chunks.accepted 2=true) (h3 : Chunks.accepted 3=true)
    (h4 : accepted 4=true) (h5 : accepted 5=true) (h6 : accepted 6=true)
    (h7 : Chunks.accepted 7=true) (i : Fin Chunks.count) : accepted i.val=true := by
  fin_cases i
  · rw [fast_eq (i:=0) (by decide)]
    have h : Chunks.baseAccepted=true ∧ Chunks.accepted 0=true := by
      simpa only [Bool.and_eq_true,decide_eq_true_eq] using h0
    exact h.2
  · rw [fast_eq (i:=1) (by decide)]
    exact h1
  · rw [fast_eq (i:=2) (by decide)]
    exact h2
  · rw [fast_eq (i:=3) (by decide)]
    exact h3
  · exact h4
  · exact h5
  · exact h6
  · rw [fast_eq (i:=7) (by decide)]
    exact h7
#print axioms cases_of_checks
end PVEvolutionA.Recovery.Mixed
