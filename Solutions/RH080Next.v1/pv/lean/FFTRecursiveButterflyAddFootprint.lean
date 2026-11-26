/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTRecursiveButterflyAddWorld
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
noncomputable section
namespace RH080Next.FFTPV.RecursiveSource

theorem add_output_outside {total : Nat} (buffers : Buffers total)
    (start index step n half j : Nat) (shape : IndexShape start index step n total)
    (split : n=2*half) (active : j<half) (input table : Nat → Nat)
    (i : Fin 4) (world : AddWorld (start+j)) (k : Nat)
    (outside : k<(start+j+half)*12 ∨ (start+j+half)*12+12≤k) :
    (addWorldAdvance buffers start index step n half j shape split active input table i world).output k=world.output k := by
  by_cases hi : i.val<2
  · simp [addWorldAdvance,addOutputData,hi]
  · let p := addWorldInput buffers start index step n half j shape split active input table i world
    have position : p.layout.start .out=(start+j+half)*12+6*(addComponent i).val := by
      simp [p,addWorldInput,butterflyAddInput,butterflyAddLayout,hi]
    have small : k<p.layout.start .out ∨ p.layout.start .out+6≤k := by
      rw [position]
      have c := (addComponent i).isLt
      rcases outside with left | right <;> omega
    have actual := AddSource.finalData_outside p k small
    simpa [addWorldAdvance,addOutputData,p,addWorldInput,butterflyAddInput,butterflyAddLayout,bufferData,hi] using actual

theorem add_work_outside {total : Nat} (buffers : Buffers total)
    (start index step n half j : Nat) (shape : IndexShape start index step n total)
    (split : n=2*half) (active : j<half) (input table : Nat → Nat)
    (i : Fin 4) (world : AddWorld (start+j)) (k : Nat) (outside : k<48 ∨ 60≤k) :
    (addWorldAdvance buffers start index step n half j shape split active input table i world).work k=world.work k := by
  by_cases hi : i.val<2
  · let p := addWorldInput buffers start index step n half j shape split active input table i world
    have position : p.layout.start .out=48+6*(addComponent i).val := by
      simp [p,addWorldInput,butterflyAddInput,butterflyAddLayout,hi]
    have small : k<p.layout.start .out ∨ p.layout.start .out+6≤k := by
      rw [position]
      have c := (addComponent i).isLt
      rcases outside with left | right <;> omega
    have actual := AddSource.finalData_outside p k small
    simpa [addWorldAdvance,addWorkData,p,addWorldInput,butterflyAddInput,butterflyAddLayout,bufferData,hi] using actual
  · simp [addWorldAdvance,addWorkData,hi]

/-- Actual four-call word footprint, strong enough for shared output slices
and the persistent main work-buffer root/accumulators. -/
theorem four_add_footprint {total : Nat} (buffers : Buffers total)
    (start index step n half j : Nat) (shape : IndexShape start index step n total)
    (split : n=2*half) (active : j<half) (input table : Nat → Nat) (world : AddWorld (start+j)) :
    let last := addWorldFour buffers start index step n half j shape split active input table world
    (∀k,(k<(start+j+half)*12 ∨ (start+j+half)*12+12≤k) → last.output k=world.output k) ∧
      (∀k,(k<48 ∨ 60≤k) → last.work k=world.work k) := by
  let next := fun i => addWorldAdvance buffers start index step n half j shape split active input table i
  have out := add_output_outside buffers start index step n half j shape split active input table
  have work := add_work_outside buffers start index step n half j shape split active input table
  constructor
  · intro k outside
    exact (out 3 (next 2 (next 1 (next 0 world))) k outside).trans
      ((out 2 (next 1 (next 0 world)) k outside).trans
        ((out 1 (next 0 world) k outside).trans (out 0 world k outside)))
  · intro k outside
    exact (work 3 (next 2 (next 1 (next 0 world))) k outside).trans
      ((work 2 (next 1 (next 0 world)) k outside).trans
        ((work 1 (next 0 world) k outside).trans (work 0 world k outside)))

#print axioms four_add_footprint
end RH080Next.FFTPV.RecursiveSource
