/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTRecursiveHeaderControl
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.RecursiveSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings ApplicationBirthFrame
namespace Header

/-- The actual right recursive call, including both permitted operand orders
of status + call and the real idempotent status store. -/
theorem View.right_call {F : Type} (context : Context F) {before childAfter : State F}
    {total : Nat} {buffers : Buffers total} {start index step n half owner cutoff : Nat}
    {ids : LoopVar → Nat} {input table output work output' work' : Nat → Nat}
    (h : View before buffers start index step n 2 ids owner input table output work)
    (shape : IndexShape start index step n total) (split : n=2*half) (positive : 0<half)
    (fresh : cutoff≤before.nextObject)
    (called : Call context "fft_recursive" (arguments (buffers.object .output) (buffers.object .input)
      (buffers.object .twiddle) (buffers.object .work) (start+half) (index+step) (step*2) half total)
      before (.value (.integer (integer64 0))) childAfter)
    (callee : ∀other result,Call context "fft_recursive" (arguments (buffers.object .output) (buffers.object .input)
      (buffers.object .twiddle) (buffers.object .work) (start+half) (index+step) (step*2) half total)
      before result other → result=.value (.integer (integer64 0)) ∧ other=childAfter)
    (frame : MultiplyCall.CallerFrame before childAfter [buffers.object .output,buffers.object .work])
    (arrays : ∀r,WordArrayRep childAfter (buffers.object r) (buffers.length r)
      (bufferData input table output' work' r)) :
    NormalSegment context before [rightRecursiveCall] childAfter ∧
      View childAfter buffers start index step n 2 ids owner input table output' work' ∧
      Frame cutoff before childAfter [buffers.object .output,buffers.object .work] := by
  have current:=h.after_call frame arrays
  have args:=h.arguments_eval context shape split positive (by decide) true
  have active : Active 2 (.inr .status) := by change 1<2;decide
  have lookup : before.environment.lookup "status"=some (scalarPointer (ids (.inr .status)) .u64) :=
    h.bindings.lookup (.inr .status) active
  have afterLookup : childAfter.environment.lookup "status"=some (scalarPointer (ids (.inr .status)) .u64) :=
    current.bindings.lookup (.inr .status) active
  have slot : Slot before (ids (.inr .status)) owner .u64 (.integer (integer64 0)) :=
    h.bindings.slots (.inr .status) active
  have afterSlot : Slot childAfter (ids (.inr .status)) owner .u64 (.integer (integer64 0)) :=
    current.bindings.slots (.inr .status) active
  have run := StatusCall.assignment_execution lookup afterLookup slot afterSlot args called
  have every : ∀other flow,Exec context before rightRecursiveCall flow other → flow=.normal ∧ other=childAfter := by
    intro other flow actual
    exact StatusCall.assignment_every_execution lookup afterLookup slot afterSlot
      (arguments_call_free true) args callee actual
  exact ⟨.single run every,current,
    ⟨frame.frame.well,fresh.trans frame.frame.nextObject,frame.frame.nextObject,frame.frame.nextScope,
      frame.frame.mode,frame.frame.foreign,fun id old absent=>frame.frame.outside id (old.trans_le fresh) absent⟩⟩

#print axioms View.right_call
end Header
end RH080Next.FFTPV.RecursiveSource
