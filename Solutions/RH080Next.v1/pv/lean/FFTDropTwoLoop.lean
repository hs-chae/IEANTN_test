/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTDropTwoStep
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.DropTwoSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings

theorem loop_unique {F : Type} (context : Context F) : CompareSource.Unique context loop:=by
  apply CompareSource.while_unique (by simp [condition,SourcePure.CallFree])
  apply CompareSource.block_unique
  intro stmt member
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at member
  rcases member with rfl|rfl
  · exact fun first second=>PureDeterminism.simple_unique (by simp [move,sourceIndex,PureDeterminism.Simple,SourcePure.CallFree]) first second
  · exact fun first second=>PureDeterminism.simple_unique (by simp [advance,PureDeterminism.Simple,SourcePure.CallFree]) first second

theorem loop_execution {F : Type} (context : Context F) (steps : Nat) {before : State F}
    {workObject owner i : Nat} {ids : Var→Nat} {old : Nat→Nat}
    (h : View before workObject ids owner i old) (remaining : i+steps=4) :
    ∃after,Exec context before loop .normal after ∧ View after workObject ids owner 4 old ∧
      ScanFrame.Frame before after [workObject,ids Var.i] ∧
      (∀other flow,Exec context before loop flow other → flow=.normal ∧ other=after) := by
  induction steps generalizing before i with
  | zero=>
    have ii : i=4:=by omega
    subst i
    have run : Exec context before loop .normal before:=.whileFalse (condition_eval context h) (by rfl)
    exact ⟨before,run,h,ScanFrame.Frame.refl before _,fun _ _ arbitrary=>by
      have eq:=loop_unique context run arbitrary;exact ⟨eq.1.symm,eq.2.symm⟩⟩
  | succ steps ih=>
    have inside : i<4:=by omega
    obtain ⟨middle,first,hm,firstFrame⟩:=step_execution context h inside
    obtain ⟨after,rest,ha,restFrame,_⟩:=ih hm (by omega)
    have ev : Eval context before condition (.integer (.boolean true)) before:=by simpa only [inside,decide_true] using condition_eval context h
    have run : Exec context before loop .normal after:=.whileNext ev (by rfl) first rest
    exact ⟨after,run,ha,firstFrame.trans restFrame,fun _ _ arbitrary=>by
      have eq:=loop_unique context run arbitrary;exact ⟨eq.1.symm,eq.2.symm⟩⟩

#print axioms loop_unique
#print axioms loop_execution
end RH080Next.FFTPV.DropTwoSource
