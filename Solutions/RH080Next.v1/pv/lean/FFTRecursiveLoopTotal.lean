/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTRecursiveMergeProgress
import FFTRecursiveWhileSegments
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
noncomputable section
namespace RH080Next.FFTPV.RecursiveSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceBindings ApplicationBirthFrame

/-- Numerical primitive domains of the actual unprocessed child cells and
sampled global twiddles. The recursive trace theorem supplies these facts. -/
structure MergeDomain (initial table : Nat → Nat) (start half stride : Nat) : Prop where
  leftNormalized : ∀r,r<half → NormalizedCell initial (start+r)
  rightNormalized : ∀r,r<half → NormalizedCell initial (start+r+half)
  twiddleNormalized : ∀r,r<half → NormalizedCell table (r*stride)
  leftNorm : ∀r,r<half → ‖FFT.IntegerModel.decode (cell initial (start+r))‖ ≤ 400
  rightNorm : ∀r,r<half → ‖FFT.IntegerModel.decode (cell initial (start+r+half))‖ ≤ 400
  twiddleNorm : ∀r,r<half → ‖FFT.IntegerModel.decode (cell table (r*stride))‖ ≤ 2

private theorem frame_restrict {F : Type} {cutoff bigger : Nat} {before after : State F} {writes : List Nat}
    (h : Frame bigger before after writes) (bound : cutoff≤bigger) : Frame cutoff before after writes :=
  ⟨h.well,bound.trans h.fresh,h.nextObject,h.nextScope,h.mode,h.foreign,
    fun id old absent => h.outside id (old.trans_le bound) absent⟩

/-- Totality and all-order correctness of the actual source while-loop,
proved by induction on its remaining real counter range. -/
theorem butterfly_loop_from {F : Type} (context : Context F) (helpers : Helpers context)
    {total : Nat} {buffers : Buffers total} {start index step n half owner : Nat}
    {ids : LoopVar → Nat} {input table initial : Nat → Nat}
    (shape : IndexShape start index step n total) (split : n=2*half)
    (domain : MergeDomain initial table start half (total/n)) (fuel : Nat)
    {before : State F} {j : Nat} {output work : Nat → Nat}
    (remaining : half-j=fuel)
    (h : LoopView before buffers start index step n ids owner j input table output work)
    (progress : MergeProgress initial table start half (total/n) j output) :
    ∃after finalOutput finalWork,
      NormalSegment context before [butterflyLoop] after ∧
      LoopView after buffers start index step n ids owner half input table finalOutput finalWork ∧
      MergeProgress initial table start half (total/n) half finalOutput ∧
      (∀k,k<buffers.length .work → 60≤k → (k<160 ∨ 172≤k) → finalWork k=work k) ∧
      Frame before.nextObject before after [buffers.object .output,buffers.object .work,ids (.inr .j)] := by
  induction fuel generalizing before j output work with
  | zero =>
    have atEnd : j=half := by have bound:=h.active;omega
    subst j
    have test : Eval context before loopCondition (.integer (.boolean false)) before := by
      simpa [show n/2=half from by omega] using loop_condition_eval context h shape
    exact ⟨before,output,work,NormalSegment.while_false (by trivial) test,h,progress,
      by intro k hk lo hi;rfl,Frame.refl _ _ h.well (le_refl _)⟩
  | succ fuel ih =>
    have active : j<half := by omega
    have words:=progress.unprocessed j (le_refl _) active
    have leftWords:=fun k hk => (words k hk).1
    have rightWords:=fun k hk => (words k hk).2
    have leftEq:=cell_congr leftWords
    have rightEq:=cell_congr rightWords
    obtain ⟨middle,nextOutput,nextWork,body,hm,left,right,leftGood,rightGood,outside,workOutside,bodyFrame⟩ :=
      butterfly_block context helpers h shape split active
        (normalized_congr leftWords (domain.leftNormalized j active))
        (normalized_congr rightWords (domain.rightNormalized j active))
        (domain.twiddleNormalized j active)
        (by rw [leftEq];exact domain.leftNorm j active)
        (by rw [rightEq];exact domain.rightNorm j active)
        (domain.twiddleNorm j active)
    have nextProgress : MergeProgress initial table start half (total/n) (j+1) nextOutput :=
      progress.next active left right leftGood rightGood outside
    obtain ⟨after,finalOutput,finalWork,rest,ha,finalProgress,finalWorkOutside,tailFrame⟩ :=
      ih (by omega) hm nextProgress
    have test : Eval context before loopCondition (.integer (.boolean true)) before := by
      simpa [show n/2=half from by omega,active] using loop_condition_eval context h shape
    have loop : NormalSegment context before [butterflyLoop] after :=
      NormalSegment.while_next (by trivial) test body rest
    exact ⟨after,finalOutput,finalWork,loop,ha,finalProgress,
      by intro k hk lo hi;exact (finalWorkOutside k hk lo hi).trans (workOutside k hk lo hi),
      bodyFrame.trans (frame_restrict tailFrame bodyFrame.nextObject)⟩

/-- Actual complete source merge from the two child output slices, including
termination, every permitted execution, exact integer merge, normalization and
physical preservation of protected caller words. -/
theorem butterfly_loop {F : Type} (context : Context F) (helpers : Helpers context)
    {before : State F} {total : Nat} {buffers : Buffers total}
    {start index step n half owner : Nat} {ids : LoopVar → Nat} {input table output work : Nat → Nat}
    (h : LoopView before buffers start index step n ids owner 0 input table output work)
    (shape : IndexShape start index step n total) (split : n=2*half)
    (domain : MergeDomain output table start half (total/n)) :
    ∃after finalOutput finalWork,
      NormalSegment context before [butterflyLoop] after ∧
      LoopView after buffers start index step n ids owner half input table finalOutput finalWork ∧
      MergeProgress output table start half (total/n) half finalOutput ∧
      (∀k,k<buffers.length .work → 60≤k → (k<160 ∨ 172≤k) → finalWork k=work k) ∧
      Frame before.nextObject before after [buffers.object .output,buffers.object .work,ids (.inr .j)] :=
  butterfly_loop_from context helpers shape split domain half (by omega) h (.zero _ _ _ _ _)

#print axioms butterfly_loop_from
#print axioms butterfly_loop
end RH080Next.FFTPV.RecursiveSource
