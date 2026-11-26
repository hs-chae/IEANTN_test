/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTAddMagnitudeStep
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.AddMagnitudeSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings
open RootSource

theorem condition_eval {F : Type} (context : Context F) {before : State F} {input : Input} {owner j : Nat} {li : Var → Nat}
    (h : View before input owner li j) : Eval context before condition (.integer (.boolean (decide (j< input.layout.n)))) before:=by
  have j64 : j<2^64:=by have a:=h.active;have n:=input.layout.small;omega
  have n64 : input.layout.n<2^64:=by have n:=input.layout.small;omega
  exact .binaryLR (.variable (h.locals.lookup Var.i) (h.locals.read Var.i)) (.variable (h.locals.lookup Var.n) (h.locals.read Var.n))
    (by simp only [values,binary,binary64_lt j input.layout.n j64 n64,Option.map_some])

theorem loop_execution {F : Type} (context : Context F) (remaining : Nat)
    {before : State F} {input : Input} {owner j : Nat} {li : Var → Nat}
    (h : View before input owner li j) (minId : ∀v,li .out≤li v) (count : j+remaining=input.layout.n) :
    ∃after,Exec context before loop .normal after ∧ View after input owner li input.layout.n ∧
      ApplicationBirthFrame.Frame (li .out) before after [input.layout.outObject] ∧ after.scope=before.scope:=by
  induction remaining generalizing before j with
  | zero=>
    have last : j=input.layout.n:=by omega
    subst j
    have oldOut:=(h.well.objectIds _ _ (h.locals.slots Var.out).object).le
    exact ⟨before,.whileFalse (condition_eval context h) (by simp [Value.truth,Integer.truth,Integer.boolean,Integer.toInt,IntKind.signed]),h,
      ApplicationBirthFrame.Frame.refl _ _ h.well oldOut,rfl⟩
  | succ remaining ih=>
    have hj : j< input.layout.n:=by omega
    obtain ⟨middle,first,post,frame1,scope1⟩:=block_execution context h minId hj
    obtain ⟨after,rest,last,frame2,scope2⟩:=ih post (by omega)
    exact ⟨after,.whileNext (condition_eval context h) (by simp [Value.truth,Integer.truth,Integer.boolean,Integer.toInt,IntKind.signed,hj]) first rest,
      last,frame1.trans frame2,scope2.trans scope1⟩

#print axioms loop_execution
end RH080Next.FFTPV.AddMagnitudeSource
