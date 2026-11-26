/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTRecursiveHeaderRight
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.RecursiveSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings ApplicationBirthFrame
namespace Header

/-- The induction premise is an actual smaller source Call contract, not a
numerical-output or initialized-state assumption. Trace/word-frame strengthenings
are proved by the full FFT induction and can be recovered from the actual calls. -/
def ChildContract {F : Type} (context : Context F) {total : Nat} (buffers : Buffers total)
    (start index step n : Nat) (input table : Nat → Nat) : Prop :=
  ∀(before : State F) (output work : Nat → Nat),WellScoped before →
    (∀r,WordArrayRep before (buffers.object r) (buffers.length r) (bufferData input table output work r)) →
    ∃after output' work',
      Call context "fft_recursive" (arguments (buffers.object .output) (buffers.object .input)
        (buffers.object .twiddle) (buffers.object .work) start index step n total)
        before (.value (.integer (integer64 0))) after ∧
      (∀r,WordArrayRep after (buffers.object r) (buffers.length r) (bufferData input table output' work' r)) ∧
      MultiplyCall.CallerFrame before after [buffers.object .output,buffers.object .work] ∧
      ∀other result,Call context "fft_recursive" (arguments (buffers.object .output) (buffers.object .input)
        (buffers.object .twiddle) (buffers.object .work) start index step n total)
        before result other → result=.value (.integer (integer64 0)) ∧ other=after

private theorem frame_empty_writes {F : Type} {cutoff : Nat} {before after : State F}
    (frame : Frame cutoff before after []) (writes : List Nat) : Frame cutoff before after writes :=
  ⟨frame.well,frame.fresh,frame.nextObject,frame.nextScope,frame.mode,frame.foreign,
    fun id old _=>frame.outside id old (by simp)⟩

/-- The actual complete nonleaf header, all declarations and both recursive
calls. The returned intermediate views expose actual current data for the
subsequent trace and outside-word preservation induction. -/
theorem View.total_header {F : Type} (context : Context F) {before : State F}
    {total : Nat} {buffers : Buffers total} {start index step n half owner : Nat}
    {ids : LoopVar → Nat} {input table output work : Nat → Nat}
    (h : View before buffers start index step n 0 ids owner input table output work)
    (shape : IndexShape start index step n total) (split : n=2*half) (positive : 0<half)
    (left : ChildContract context buffers start index (step*2) half input table)
    (right : ChildContract context buffers (start+half) (index+step) (step*2) half input table) :
    ∃after finalIds leftBefore leftAfter rightBefore rightAfter leftIds rightIds leftOutput leftWork finalOutput finalWork,
      NormalSegment context before (functionStatements.take 7) after ∧
      LoopView after buffers start index step n finalIds owner 0 input table finalOutput finalWork ∧
      Frame before.nextObject before after [buffers.object .output,buffers.object .work] ∧
      View leftBefore buffers start index step n 1 leftIds owner input table output work ∧
      Call context "fft_recursive" (arguments (buffers.object .output) (buffers.object .input)
        (buffers.object .twiddle) (buffers.object .work) start index (step*2) half total)
        leftBefore (.value (.integer (integer64 0))) leftAfter ∧
      (∀r,WordArrayRep leftAfter (buffers.object r) (buffers.length r)
        (bufferData input table leftOutput leftWork r)) ∧
      View rightBefore buffers start index step n 2 rightIds owner input table leftOutput leftWork ∧
      Call context "fft_recursive" (arguments (buffers.object .output) (buffers.object .input)
        (buffers.object .twiddle) (buffers.object .work) (start+half) (index+step) (step*2) half total)
        rightBefore (.value (.integer (integer64 0))) rightAfter ∧
      (∀r,WordArrayRep rightAfter (buffers.object r) (buffers.length r)
        (bufferData input table finalOutput finalWork r)) := by
  have hn:=shape.scalar_bounds.2.2.2.1
  have branch:=h.nonleaf_branch context hn (by omega)
  obtain ⟨leftBefore,halfRun,h1,f1⟩:=h.half_birth context hn (le_refl _)
  obtain ⟨leftAfter,leftOutput,leftWork,leftCall,leftArrays,leftFrame,leftEvery⟩:=
    left leftBefore output work h1.well h1.arrays
  obtain ⟨rightBefore,statusRun,h2,f2⟩:=h1.status_birth context shape split positive f1.fresh
    leftCall leftEvery leftFrame leftArrays
  obtain ⟨rightAfter,finalOutput,finalWork,rightCall,rightArrays,rightFrame,rightEvery⟩:=
    right rightBefore leftOutput leftWork h2.well h2.arrays
  obtain ⟨rightRun,h3,f3⟩:=h2.right_call context shape split positive f2.fresh
    rightCall rightEvery rightFrame rightArrays
  obtain ⟨after,finalIds,tailRun,finished,f4⟩:=h3.tail_births context shape f3.fresh
  refine ⟨after,finalIds,leftBefore,leftAfter,rightBefore,rightAfter,_,_,leftOutput,leftWork,finalOutput,finalWork,
    ?_,finished,?_,h1,leftCall,leftArrays,h2,rightCall,rightArrays⟩
  · have all:=(((branch.append halfRun).append statusRun).append rightRun).append tailRun
    exact all
  · exact (((frame_empty_writes f1 _).trans f2).trans f3).trans (frame_empty_writes f4 _)

#print axioms View.total_header
end Header
end RH080Next.FFTPV.RecursiveSource
