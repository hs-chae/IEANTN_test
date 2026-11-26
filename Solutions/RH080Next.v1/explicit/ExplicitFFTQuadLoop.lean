/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTQuadRow
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.QuadSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings
open InputLoader RootSource

theorem LoopView.condition_eval {F : Type} (context : Context F) {before : State F} {input : InputLoader.Input} {workObject fo j : Nat}
    {paramIds : Parameter → Nat} {auxIds : Aux → Nat} {dataMemory workData : Nat → Nat}
    (h : LoopView before input workObject fo j paramIds auxIds dataMemory workData) :
    Eval context before (.binary .lt (.variable "j") (.literal (.integer input.profile.count "ULL")))
      (.integer (.boolean (decide (j< input.profile.count)))) before:=by
  have shape:=input.profile.shape
  have j64 : j<2^64:=by have active:=h.active;omega
  have count64 : input.profile.count<2^64:=by omega
  exact .binaryLR (.variable (h.parameters.lookup .j) (h.parameters.read .j))
    (.literal (.integer input.profile.count "ULL") _ (.integer (integer64 input.profile.count))
      (by have b : input.profile.count<18446744073709551616:=count64;simp [Literal.value,integer64,b]))
    (by simp only [parameterValues,binary,CompareSource.binary64_lt j input.profile.count j64 count64,Option.map_some])

theorem loop_execution {F : Type} (context : Context F) (remaining : Nat)
    {before : State F} {input : InputLoader.Input} {workObject fo j cutoff : Nat}
    {paramIds : Parameter → Nat} {auxIds : Aux → Nat} {dataMemory workData : Nat → Nat}
    (h : LoopView before input workObject fo j paramIds auxIds dataMemory workData) (pinned : context.program=input.profile.program)
    (count : j+remaining=input.profile.count) (fresh : cutoff≤ before.nextObject) :
    ∃after memory,Exec context before (loop input.profile) .normal after ∧ Every context before (loop input.profile) .normal after ∧
      LoopView after input workObject fo input.profile.count paramIds auxIds dataMemory memory ∧
      ApplicationBirthFrame.Frame cutoff before after [workObject,paramIds .j] ∧
      after.environment=before.environment ∧ after.scope=before.scope ∧
      ∀k,(k<160 ∨ 166≤ k) → (k<208 ∨ 214≤ k) → memory k=workData k:=by
  induction remaining generalizing before j workData with
  | zero=>
    have last : j=input.profile.count:=by omega
    subst j
    have test : (.integer (.boolean (decide (input.profile.count< input.profile.count))) : Value).truth=some false:=by
      simp [Value.truth,Integer.truth,Integer.boolean,Integer.toInt,IntKind.signed]
    exact ⟨before,workData,.whileFalse (h.condition_eval context) test,every_while_false (by trivial) (h.condition_eval context) test,h,
      ApplicationBirthFrame.Frame.refl _ _ h.well fresh,rfl,rfl,fun _ _ _=> rfl⟩
  | succ remaining ih=>
    have hj : j< input.profile.count:=by omega
    obtain ⟨middle,memory,first,firstEvery,post,frame1,env1,scope1,outside1⟩:=row_execution context h pinned hj
    have firstFrame:=lower_frame frame1 fresh
    obtain ⟨after,finalMemory,rest,restEvery,last,frame2,env2,scope2,outside2⟩:=ih post (by omega) firstFrame.fresh
    have test : (.integer (.boolean (decide (j< input.profile.count))) : Value).truth=some true:=by
      simp [Value.truth,Integer.truth,Integer.boolean,Integer.toInt,IntKind.signed,hj]
    exact ⟨after,finalMemory,.whileNext (h.condition_eval context) test first rest,
      every_while_next (by trivial) (h.condition_eval context) test firstEvery restEvery,last,firstFrame.trans frame2,env2.trans env1,scope2.trans scope1,
      fun k ht hq=>(outside2 k ht hq).trans (outside1 k ht hq)⟩

#print axioms loop_execution
end RH080Next.FFTPV.QuadSource
