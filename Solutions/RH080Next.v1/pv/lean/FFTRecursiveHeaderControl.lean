/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTRecursiveHeaderBirths
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.RecursiveSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings ApplicationBirthFrame
namespace Header

theorem View.nonleaf_test {F : Type} (context : Context F) {before : State F}
    {total : Nat} {buffers : Buffers total} {start index step n count owner : Nat}
    {ids : LoopVar → Nat} {input table output work : Nat → Nat}
    (h : View before buffers start index step n count ids owner input table output work)
    (hn : n<2^64) (different : n≠1) :
    Eval context before leafCondition (.integer (.boolean false)) before := by
  refine .binaryLR (h.parameter context .n)
    (.literal (.integer 1 "ULL") _ (.integer (integer64 1)) (by rfl)) ?_
  change some (Value.integer (Integer.boolean ((Integer.cast .u64 (integer64 n).toInt).toInt ==
    (Integer.cast .u64 (integer64 1).toInt).toInt))) = _
  rw [integer64_toInt,integer64_toInt,cast64_exact n hn,cast64_exact 1 (by norm_num),
    integer64_toInt,integer64_toInt]
  have neInt : (n:Int)≠1 := by exact_mod_cast different
  have beq : ((n:Int)==1)=false := beq_eq_false_iff_ne.mpr neInt
  simp only [Nat.cast_one,beq]

/-- The source really takes its nonleaf branch, for all evaluation orders. -/
theorem View.nonleaf_branch {F : Type} (context : Context F) {before : State F}
    {total : Nat} {buffers : Buffers total} {start index step n count owner : Nat}
    {ids : LoopVar → Nat} {input table output work : Nat → Nat}
    (h : View before buffers start index step n count ids owner input table output work)
    (hn : n<2^64) (different : n≠1) : NormalSegment context before [leafBranch] before := by
  have test:=h.nonleaf_test context hn different
  refine .single (.ifFalse test (by rfl)) ?_
  intro other flow actual
  cases actual with
  | ifFalse ev truth =>
    obtain ⟨rfl,rfl⟩:=PureDeterminism.eval_unique (by trivial) test ev
    exact ⟨rfl,rfl⟩
  | ifTrue ev truth body =>
    obtain ⟨rfl,rfl⟩:=PureDeterminism.eval_unique (by trivial) test ev
    cases truth

/-- The real status declaration initializes only after the actual left child
has returned. The general child correctness theorem is an induction premise. -/
theorem View.status_birth {F : Type} (context : Context F) {before childAfter : State F}
    {total : Nat} {buffers : Buffers total} {start index step n half owner cutoff : Nat}
    {ids : LoopVar → Nat} {input table output work output' work' : Nat → Nat}
    (h : View before buffers start index step n 1 ids owner input table output work)
    (shape : IndexShape start index step n total) (split : n=2*half) (positive : 0<half)
    (fresh : cutoff≤before.nextObject)
    (called : Call context "fft_recursive" (arguments (buffers.object .output) (buffers.object .input)
      (buffers.object .twiddle) (buffers.object .work) start index (step*2) half total)
      before (.value (.integer (integer64 0))) childAfter)
    (callee : ∀other result,Call context "fft_recursive" (arguments (buffers.object .output) (buffers.object .input)
      (buffers.object .twiddle) (buffers.object .work) start index (step*2) half total)
      before result other → result=.value (.integer (integer64 0)) ∧ other=childAfter)
    (frame : MultiplyCall.CallerFrame before childAfter [buffers.object .output,buffers.object .work])
    (arrays : ∀r,WordArrayRep childAfter (buffers.object r) (buffers.length r)
      (bufferData input table output' work' r)) :
    ∃after,NormalSegment context before [statusDeclaration] after ∧
      View after buffers start index step n 2 (Function.update ids (.inr .status) childAfter.nextObject)
        owner input table output' work' ∧ Frame cutoff before after [buffers.object .output,buffers.object .work] := by
  have current:=h.after_call frame arrays
  have args:=h.arguments_eval context shape split positive (by decide) false
  have sz:=ZeroFrame.u64_storable 0 (by norm_num)
  obtain ⟨after,declared⟩:=ZeroFrame.declare_exists current.well .u64 "status" (.integer (integer64 0)) sz
  have d:=declare_storable sz sz.converted declared
  have exec : Exec context before statusDeclaration .normal after :=
    .declareSome (.call args called) declared
  have every : ∀other flow,Exec context before statusDeclaration flow other → flow=.normal ∧ other=after := by
    intro other flow actual
    cases actual with
    | declareSome ev dec =>
      obtain ⟨rfl,rfl⟩:=StatusCall.call_eval_unique (arguments_call_free false) args callee ev
      exact ⟨rfl,Option.some.inj (dec.symm.trans declared)⟩
  have cf : Frame cutoff before childAfter [buffers.object .output,buffers.object .work] :=
    ⟨frame.frame.well,fresh.trans frame.frame.nextObject,frame.frame.nextObject,frame.frame.nextScope,
      frame.frame.mode,frame.frame.foreign,fun id old absent=>frame.frame.outside id (old.trans_le fresh) absent⟩
  exact ⟨after,.single exec every,current.declare rfl d declared,
    cf.trans (ApplicationBirthFrame.declare_frame cutoff _ current.well cf.fresh declared)⟩

#print axioms View.nonleaf_test
#print axioms View.nonleaf_branch
#print axioms View.status_birth
end Header
end RH080Next.FFTPV.RecursiveSource
