/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTInputLoaderRow
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.InputLoader
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings
open RootSource

theorem LoopView.condition_eval {F : Type} (context : Context F) {before : State F} {input : Input} {fo j : Nat} {ids : Parameter → Nat}
    (h : LoopView before input fo ids j) :
    Eval context before (.binary .lt (.variable "j") (.literal (.integer input.profile.count "ULL")))
      (.integer (.boolean (decide (j< input.profile.count)))) before:=by
  have shape:=input.profile.shape
  have j64 : j<2^64:=by have active:=h.active;omega
  have count64 : input.profile.count<2^64:=by omega
  exact .binaryLR (.variable (h.locals.lookup .j) (h.locals.read .j))
    (.literal (.integer input.profile.count "ULL") _ (.integer (integer64 input.profile.count))
      (by have b : input.profile.count<18446744073709551616:=count64;simp [Literal.value,integer64,b]))
    (by simp only [parameterValues,binary,CompareSource.binary64_lt j input.profile.count j64 count64,Option.map_some])

/-- Total execution and every-order correctness of the entire actual source
input loop. The induction covers all400/2520 source rows and each reflected
copy; no initialized numerical vector or completed loop is assumed. -/
theorem loop_execution {F : Type} (context : Context F) (remaining : Nat)
    {before : State F} {input : Input} {fo j cutoff : Nat} {ids : Parameter → Nat}
    (h : LoopView before input fo ids j) (pinned : context.program=input.profile.program)
    (count : j+remaining=input.profile.count) (fresh : cutoff≤before.nextObject) :
    ∃after,Exec context before (loop input.profile.count) .normal after ∧ Every context before (loop input.profile.count) .normal after ∧
      LoopView after input fo ids input.profile.count ∧ ApplicationBirthFrame.Frame cutoff before after [input.object,ids .j] ∧
      after.environment=before.environment ∧ after.scope=before.scope:=by
  induction remaining generalizing before j with
  | zero=>
    have last : j=input.profile.count:=by omega
    subst j
    have test : (.integer (.boolean (decide (input.profile.count< input.profile.count))) : Value).truth=some false:=by
      simp [Value.truth,Integer.truth,Integer.boolean,Integer.toInt,IntKind.signed]
    exact ⟨before,.whileFalse (h.condition_eval context) test,every_while_false (by trivial) (h.condition_eval context) test,h,
      ApplicationBirthFrame.Frame.refl _ _ h.well fresh,rfl,rfl⟩
  | succ remaining ih=>
    have hj : j< input.profile.count:=by omega
    obtain ⟨middle,first,firstEvery,post,frame1,env1,scope1⟩:=row_execution context h pinned hj
    have firstFrame:=lower_frame frame1 fresh
    obtain ⟨after,rest,restEvery,last,frame2,env2,scope2⟩:=ih post (by omega) firstFrame.fresh
    have test : (.integer (.boolean (decide (j< input.profile.count))) : Value).truth=some true:=by
      simp [Value.truth,Integer.truth,Integer.boolean,Integer.toInt,IntKind.signed,hj]
    exact ⟨after,.whileNext (h.condition_eval context) test first rest,
      every_while_next (by trivial) (h.condition_eval context) test firstEvery restEvery,last,firstFrame.trans frame2,env2.trans env1,scope2.trans scope1⟩

#print axioms loop_execution
end RH080Next.FFTPV.InputLoader
