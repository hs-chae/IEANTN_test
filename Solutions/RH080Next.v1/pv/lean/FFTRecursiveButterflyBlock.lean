/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTRecursiveButterflyContents
import FFTRecursiveLeafCall
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
noncomputable section
namespace RH080Next.FFTPV.RecursiveSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceBindings ApplicationBirthFrame

/-- The real butterfly block closes its fresh a/b/w scope. Persistent source
bindings and all four host arrays survive the actual leaveScope operation. -/
theorem butterfly_block {F : Type} (context : Context F) (helpers : Helpers context)
    {before : State F} {total : Nat} {buffers : Buffers total}
    {start index step n half j owner : Nat} {ids : LoopVar → Nat} {input table output work : Nat → Nat}
    (h : LoopView before buffers start index step n ids owner j input table output work)
    (shape : IndexShape start index step n total) (split : n=2*half) (active : j<half)
    (leftNormalized : NormalizedCell output (start+j))
    (rightNormalized : NormalizedCell output (start+j+half))
    (twiddleNormalized : NormalizedCell table (j*(total/n)))
    (leftNorm : ‖FFT.IntegerModel.decode (cell output (start+j))‖ ≤ 400)
    (rightNorm : ‖FFT.IntegerModel.decode (cell output (start+j+half))‖ ≤ 400)
    (twiddleNorm : ‖FFT.IntegerModel.decode (cell table (j*(total/n)))‖ ≤ 2) :
    ∃after newOutput newWork,
      NormalSegment context before [.block butterflyStatements] after ∧
      LoopView after buffers start index step n ids owner (j+1) input table newOutput newWork ∧
      cell newOutput (start+j) = FFT.IntegerModel.add (cell output (start+j))
        (FFT.IntegerModel.mul (cell output (start+j+half)) (cell table (j*(total/n)))) ∧
      cell newOutput (start+j+half) = FFT.IntegerModel.sub (cell output (start+j))
        (FFT.IntegerModel.mul (cell output (start+j+half)) (cell table (j*(total/n)))) ∧
      NormalizedCell newOutput (start+j) ∧ NormalizedCell newOutput (start+j+half) ∧
      (∀k,(k<(start+j)*12 ∨ (start+j)*12+12≤k) →
        (k<(start+j+half)*12 ∨ (start+j+half)*12+12≤k) → newOutput k=output k) ∧
      (∀k,k<buffers.length .work → 60≤k → (k<160 ∨ 172≤k) → newWork k=work k) ∧
      Frame before.nextObject before after [buffers.object .output,buffers.object .work,ids (.inr .j)] := by
  obtain ⟨middle,newOutput,newWork,contents,hm,left,right,leftGood,rightGood,outside,workOutside,frame⟩ :=
    butterfly_contents context helpers h.enter shape split active leftNormalized rightNormalized
      twiddleNormalized leftNorm rightNorm twiddleNorm
  let after : State F := {middle.leaveScope before.nextScope before.environment with scope:=before.scope}
  have closedFrame : Frame before.nextObject before after
      [buffers.object .output,buffers.object .work,ids (.inr .j)] := close_frame h.well (le_refl _) frame
  have closed : LoopView after buffers start index step n ids owner (j+1) input table newOutput newWork := by
    refine ⟨hm.bindings.leave (fun v => ?_) before.environment h.bindings.lookup,
      fun r => word_array_leave (hm.arrays r) before.environment,closedFrame.well,hm.active⟩
    have bound:=h.bindings.bound v
    omega
  have run : Exec context before (.block butterflyStatements) .normal after :=
    .block rfl contents.execution rfl
  have every : ∀other flow,Exec context before (.block butterflyStatements) flow other →
      flow=.normal ∧ other=after := by
    intro other flow actual
    cases actual with
    | block entered body finished =>
      subst_vars
      obtain ⟨rfl,rfl⟩ := contents.every _ _ body
      exact ⟨rfl,rfl⟩
  exact ⟨after,newOutput,newWork,.single run every,closed,left,right,leftGood,rightGood,
    outside,workOutside,closedFrame⟩

#print axioms butterfly_block
end RH080Next.FFTPV.RecursiveSource
