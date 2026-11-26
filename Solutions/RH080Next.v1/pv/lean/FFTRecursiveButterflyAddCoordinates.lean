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

def addCoordinate {left : Nat} (world : AddWorld left) (right : Nat) (i : Fin 4) : Int :=
  if i.val<2 then CanonicalSource.represented world.work (48+6*(addComponent i).val)
  else CanonicalSource.represented world.output (right*12+6*(addComponent i).val)

def expectedAddCoordinate {left : Nat} (world : AddWorld left) (i : Fin 4) : Int :=
  if i.val<2 then
    CanonicalSource.represented world.output (left*12+6*(addComponent i).val)+
      CanonicalSource.represented world.work (160+6*(addComponent i).val)
  else
    CanonicalSource.represented world.output (left*12+6*(addComponent i).val)-
      CanonicalSource.represented world.work (160+6*(addComponent i).val)

/-- Actual source data update sets precisely the selected butterfly scalar. -/
theorem add_coordinate_self {total : Nat} (buffers : Buffers total)
    (start index step n half j : Nat) (shape : IndexShape start index step n total)
    (split : n=2*half) (active : j<half) (input table : Nat → Nat)
    (i : Fin 4) (world : AddWorld (start+j)) :
    addCoordinate (addWorldAdvance buffers start index step n half j shape split active input table i world)
      (start+j+half) i = expectedAddCoordinate world i := by
  let p := addWorldInput buffers start index step n half j shape split active input table i world
  have zero : AddSource.rawStatus p=0 := butterfly_add_status_zero buffers start index step n half j shape split active i
    input table world.output world.work world.facts.leftNormalized world.facts.tempDigits world.facts.tempSigns
    world.facts.leftNorm world.facts.tempNorm
  have actual := AddSource.finalData_integer_correct p zero
  by_cases hi : i.val<2
  · simpa [p,addCoordinate,expectedAddCoordinate,addWorldAdvance,addWorldInput,addOutputData,addWorkData,
      butterflyAddInput,butterflyAddLayout,bufferData,hi] using actual
  · simpa [p,addCoordinate,expectedAddCoordinate,addWorldAdvance,addWorldInput,addOutputData,addWorkData,
      butterflyAddInput,butterflyAddLayout,bufferData,hi] using actual

/-- Different scalar destinations of the four source calls are disjoint;
previously proved output coordinates are not overwritten. -/
theorem add_coordinate_other {total : Nat} (buffers : Buffers total)
    (start index step n half j : Nat) (shape : IndexShape start index step n total)
    (split : n=2*half) (active : j<half) (input table : Nat → Nat)
    (i target : Fin 4) (world : AddWorld (start+j)) (different : i≠target) :
    addCoordinate (addWorldAdvance buffers start index step n half j shape split active input table i world)
      (start+j+half) target = addCoordinate world (start+j+half) target := by
  let p := addWorldInput buffers start index step n half j shape split active input table i world
  have ni : i.val<4 := i.isLt
  have nt : target.val<4 := target.isLt
  have ne : i.val≠target.val := by intro same;exact different (Fin.ext same)
  by_cases hi : i.val<2
  · by_cases ht : target.val<2
    · simp only [addCoordinate,ht,↓reduceIte,addWorldAdvance,addWorkData,hi]
      apply represented_congr
      intro k hk
      have disjoint : 48+6*(addComponent target).val+k < p.layout.start .out ∨
          p.layout.start .out+6 ≤ 48+6*(addComponent target).val+k := by
        have position : p.layout.start .out=48+6*(addComponent i).val := by
          simp [p,addWorldInput,butterflyAddInput,butterflyAddLayout,hi]
        rw [position]
        simp only [addComponent]
        omega
      have actual := AddSource.finalData_outside p (48+6*(addComponent target).val+k) disjoint
      simpa [p,addWorldInput,butterflyAddInput,butterflyAddLayout,bufferData,hi] using actual
    · simp [addCoordinate,ht,addWorldAdvance,addOutputData,hi]
  · by_cases ht : target.val<2
    · simp [addCoordinate,ht,addWorldAdvance,addWorkData,hi]
    · simp only [addCoordinate,ht,↓reduceIte,addWorldAdvance,addOutputData,hi]
      apply represented_congr
      intro k hk
      have disjoint : (start+j+half)*12+6*(addComponent target).val+k < p.layout.start .out ∨
          p.layout.start .out+6 ≤ (start+j+half)*12+6*(addComponent target).val+k := by
        have position : p.layout.start .out=(start+j+half)*12+6*(addComponent i).val := by
          simp [p,addWorldInput,butterflyAddInput,butterflyAddLayout,hi]
        rw [position]
        simp only [addComponent]
        omega
      have actual := AddSource.finalData_outside p ((start+j+half)*12+6*(addComponent target).val+k) disjoint
      simpa [p,addWorldInput,butterflyAddInput,butterflyAddLayout,bufferData,hi] using actual

/-- Left and product operands survive every actual source-data update, so all
four results refer to the same mathematical butterfly inputs. -/
theorem expected_coordinate_stable {total : Nat} (buffers : Buffers total)
    (start index step n half j : Nat) (shape : IndexShape start index step n total)
    (split : n=2*half) (active : j<half) (input table : Nat → Nat)
    (i target : Fin 4) (world : AddWorld (start+j)) :
    expectedAddCoordinate (addWorldAdvance buffers start index step n half j shape split active input table i world) target =
      expectedAddCoordinate world target := by
  have leftWords := add_left_untouched buffers start index step n half j shape split active i
    input table world.output world.work world.facts.leftNormalized world.facts.tempDigits world.facts.tempSigns
  have tempWords := add_temp_untouched buffers start index step n half j shape split active i
    input table world.output world.work world.facts.leftNormalized world.facts.tempDigits world.facts.tempSigns
  have left : CanonicalSource.represented
      (addWorldAdvance buffers start index step n half j shape split active input table i world).output
      ((start+j)*12+6*(addComponent target).val) =
      CanonicalSource.represented world.output ((start+j)*12+6*(addComponent target).val) := by
    apply represented_congr
    intro k hk
    simpa only [addWorldAdvance,addWorldInput,Nat.add_assoc] using
      leftWords (6*(addComponent target).val+k) (by have h := (addComponent target).isLt;omega)
  have temp : CanonicalSource.represented
      (addWorldAdvance buffers start index step n half j shape split active input table i world).work
      (160+6*(addComponent target).val) = CanonicalSource.represented world.work (160+6*(addComponent target).val) := by
    apply represented_congr
    intro k hk
    simpa only [addWorldAdvance,addWorldInput,Nat.add_assoc] using
      tempWords (6*(addComponent target).val+k) (by have h := (addComponent target).isLt;omega)
  simp only [expectedAddCoordinate,left,temp]

/-- Four actual five-digit add/subtract source algorithms implement the four
scalar outputs of a mathematical complex butterfly. -/
theorem four_add_coordinates {total : Nat} (buffers : Buffers total)
    (start index step n half j : Nat) (shape : IndexShape start index step n total)
    (split : n=2*half) (active : j<half) (input table : Nat → Nat) (world : AddWorld (start+j)) :
    ∀i : Fin 4,addCoordinate (addWorldFour buffers start index step n half j shape split active input table world)
      (start+j+half) i = expectedAddCoordinate world i := by
  let next := fun i => addWorldAdvance buffers start index step n half j shape split active input table i
  have other := add_coordinate_other buffers start index step n half j shape split active input table
  have same := add_coordinate_self buffers start index step n half j shape split active input table
  have stable := expected_coordinate_stable buffers start index step n half j shape split active input table
  intro i
  change addCoordinate (next 3 (next 2 (next 1 (next 0 world)))) (start+j+half) i = _
  fin_cases i
  · exact (other 3 0 (next 2 (next 1 (next 0 world))) (by decide)).trans
      ((other 2 0 (next 1 (next 0 world)) (by decide)).trans
        ((other 1 0 (next 0 world) (by decide)).trans (same 0 world)))
  · exact (other 3 1 (next 2 (next 1 (next 0 world))) (by decide)).trans
      ((other 2 1 (next 1 (next 0 world)) (by decide)).trans
        ((same 1 (next 0 world)).trans (stable 0 1 world)))
  · exact (other 3 2 (next 2 (next 1 (next 0 world))) (by decide)).trans
      ((same 2 (next 1 (next 0 world))).trans
        ((stable 1 2 (next 0 world)).trans (stable 0 2 world)))
  · exact (same 3 (next 2 (next 1 (next 0 world)))).trans
      ((stable 2 3 (next 1 (next 0 world))).trans
        ((stable 1 3 (next 0 world)).trans (stable 0 3 world)))

#print axioms four_add_coordinates
end RH080Next.FFTPV.RecursiveSource
