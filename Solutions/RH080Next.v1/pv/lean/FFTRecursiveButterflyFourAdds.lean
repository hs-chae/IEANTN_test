/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTRecursiveButterflyAddStatement
import FFTRecursiveButterflyAddWorld
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
noncomputable section
namespace RH080Next.FFTPV.RecursiveSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceBindings ApplicationBirthFrame

private theorem widen_frame {F : Type} {before after : State F} {writes allWrites : List Nat}
    (frame : MultiplyCall.CallerFrame before after writes) (cutoff : Nat)
    (bound : cutoff≤before.nextObject) (subset : ∀id∈writes,id∈allWrites) :
    Frame cutoff before after allWrites := by
  refine ⟨frame.frame.well,bound.trans frame.frame.nextObject,frame.frame.nextObject,
    frame.frame.nextScope,frame.frame.mode,frame.frame.foreign,?_⟩
  intro id old absent
  apply frame.frame.outside id (old.trans_le bound)
  intro member
  exact absent (subset id member)

/-- One actual source operation follows the exact source digit-data update. -/
theorem add_world_execution {F : Type} (context : Context F) (helpers : Helpers context)
    {before : State F} {total : Nat} {buffers : Buffers total}
    {start index step n half j owner pointerOwner : Nat} {ids : LoopVar → Nat} {pids : PointerVar → Nat}
    {input table : Nat → Nat} (world : AddWorld (start+j))
    (h : LoopView before buffers start index step n ids owner j input table world.output world.work)
    (pointers : Locals before pointerName pointerType pids pointerOwner (pointerValue buffers start n half j))
    (shape : IndexShape start index step n total) (split : n=2*half) (active : j<half) (i : Fin 4) :
    let next := addWorldAdvance buffers start index step n half j shape split active input table i world
    ∃after, NormalSegment context before [StatusCall.statement "fixed_add" (butterflyArguments ⟨i.val+1,by omega⟩)] after ∧
      LoopView after buffers start index step n ids owner j input table next.output next.work ∧
      Locals after pointerName pointerType pids pointerOwner (pointerValue buffers start n half j) ∧
      MultiplyCall.CallerFrame before after [(addWorldInput buffers start index step n half j shape split active input table i world).layout.object .out] := by
  dsimp only
  simpa only [addWorldAdvance,addWorldInput] using butterfly_add_statement context helpers h pointers shape split active i
    world.facts.leftNormalized world.facts.tempDigits world.facts.tempSigns world.facts.leftNorm world.facts.tempNorm

/-- All four genuine fixed_add/status statements execute in source order and
agree for every permitted evaluation order. The word functions are exactly
four applications of the already proved source digit/sign algorithm. -/
theorem four_adds_execution {F : Type} (context : Context F) (helpers : Helpers context)
    {before : State F} {total : Nat} {buffers : Buffers total}
    {start index step n half j owner pointerOwner : Nat} {ids : LoopVar → Nat} {pids : PointerVar → Nat}
    {input table : Nat → Nat} (world : AddWorld (start+j))
    (h : LoopView before buffers start index step n ids owner j input table world.output world.work)
    (pointers : Locals before pointerName pointerType pids pointerOwner (pointerValue buffers start n half j))
    (shape : IndexShape start index step n total) (split : n=2*half) (active : j<half) :
    let last := addWorldFour buffers start index step n half j shape split active input table world
    ∃after, NormalSegment context before ((butterflyStatements.drop 4).take 4) after ∧
      LoopView after buffers start index step n ids owner j input table last.output last.work ∧
      Locals after pointerName pointerType pids pointerOwner (pointerValue buffers start n half j) ∧
      Frame before.nextObject before after [buffers.object .output,buffers.object .work] := by
  dsimp only
  let next := fun i => addWorldAdvance buffers start index step n half j shape split active input table i
  let w1 := next 0 world
  let w2 := next 1 w1
  let w3 := next 2 w2
  let w4 := next 3 w3
  obtain ⟨s1,e1,h1,p1,f1⟩ := add_world_execution context helpers world h pointers shape split active 0
  change LoopView s1 buffers start index step n ids owner j input table w1.output w1.work at h1
  obtain ⟨s2,e2,h2,p2,f2⟩ := add_world_execution context helpers w1 h1 p1 shape split active 1
  change LoopView s2 buffers start index step n ids owner j input table w2.output w2.work at h2
  obtain ⟨s3,e3,h3,p3,f3⟩ := add_world_execution context helpers w2 h2 p2 shape split active 2
  change LoopView s3 buffers start index step n ids owner j input table w3.output w3.work at h3
  obtain ⟨s4,e4,h4,p4,f4⟩ := add_world_execution context helpers w3 h3 p3 shape split active 3
  change LoopView s4 buffers start index step n ids owner j input table w4.output w4.work at h4
  have whole : NormalSegment context before ((butterflyStatements.drop 4).take 4) s4 := by
    simpa [butterflyStatements] using ((e1.append e2).append e3).append e4
  have g1 : Frame before.nextObject before s1 [buffers.object .output,buffers.object .work] :=
    widen_frame f1 _ (le_refl _) (by
      intro id member
      have same : id=buffers.object .work := by
        simpa [addWorldInput,butterflyAddInput,butterflyAddLayout] using member
      simp [same])
  have g2 : Frame before.nextObject s1 s2 [buffers.object .output,buffers.object .work] :=
    widen_frame f2 _ g1.fresh (by
      intro id member
      have same : id=buffers.object .work := by
        simpa [addWorldInput,butterflyAddInput,butterflyAddLayout] using member
      simp [same])
  have g3 : Frame before.nextObject s2 s3 [buffers.object .output,buffers.object .work] :=
    widen_frame f3 _ g2.fresh (by
      intro id member
      have same : id=buffers.object .output := by
        simpa [addWorldInput,butterflyAddInput,butterflyAddLayout] using member
      simp [same])
  have g4 : Frame before.nextObject s3 s4 [buffers.object .output,buffers.object .work] :=
    widen_frame f4 _ g3.fresh (by
      intro id member
      have same : id=buffers.object .output := by
        simpa [addWorldInput,butterflyAddInput,butterflyAddLayout] using member
      simp [same])
  exact ⟨s4,whole,h4,p4,((g1.trans g2).trans g3).trans g4⟩

#print axioms four_adds_execution
end RH080Next.FFTPV.RecursiveSource
