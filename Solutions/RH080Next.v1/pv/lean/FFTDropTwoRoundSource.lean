/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTDropTwoRounding
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.DropTwoSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings
open ApplicationBirthFrame

private theorem lost_fits {old : Nat→Nat} (digits : ∀k,k<6 → old (192+k)<base) : lost old 192<2^64:=by
  have h0:=digits 0 (by norm_num)
  have h1:=digits 1 (by norm_num)
  dsimp [lost,base] at *
  omega

theorem rounding_execution {F : Type} (context : Context F)
    (selected : findFunction context.program "increment_words"=some increment_words_ast)
    {before : State F} {workObject owner : Nat} {ids : Var→Nat} {old : Nat→Nat}
    (array : WordArrayRep before workObject 512 (dropped old 192))
    (params : Locals before name type ids owner (values workObject old 4))
    (separate : ∀v,workObject≠ids v) (digits : ∀k,k<6 → old (192+k)<base) (well : WellScoped before) :
    ∃after,Exec context before roundingBranch .normal after ∧
      WordArrayRep after workObject 512 (roundData old 192) ∧
      Locals after name type ids owner (values workObject old 4) ∧
      Frame before.nextObject before after [workObject] ∧
      (∀other flow,Exec context before roundingBranch flow other → flow=.normal ∧ other=after) := by
  have ev : Eval context before roundingTest (.integer (.boolean (decide (0<lost old 192)))) before:=
    .binaryLR (.variable (params.lookup Var.lost) (params.read Var.lost))
      (.literal (.integer 0 "ULL") _ (.integer (integer64 0)) (by rfl))
      (by simp only [values,binary,CompareSource.binary64_gt (lost old 192) 0 (lost_fits digits) (by norm_num),Option.map_some])
  by_cases hz : lost old 192=0
  · have run : Exec context before roundingBranch .normal before:=
      .ifFalse ev (by simp [Value.truth,Integer.truth,Integer.boolean,Integer.toInt,IntKind.signed,hz])
    refine ⟨before,run,by simpa only [roundData,if_pos hz] using array,params,Frame.refl before.nextObject _ well (le_refl _),?_⟩
    intro other flow arbitrary
    cases arbitrary with
    | ifFalse actual truth=>
      obtain ⟨_,eqs⟩:=PureDeterminism.eval_unique (by simp [roundingTest,SourcePure.CallFree]) ev actual
      exact ⟨rfl,eqs.symm⟩
    | ifTrue actual truth body=>
      obtain ⟨rfl,rfl⟩:=PureDeterminism.eval_unique (by simp [roundingTest,SourcePure.CallFree]) ev actual
      simp [Value.truth,Integer.truth,Integer.boolean,Integer.toInt,IntKind.signed,hz] at truth
  · have positive : 0<lost old 192:=by omega
    let entered:=before.enterScope
    obtain ⟨middle,called,rep,fullFrame⟩:=IncrementSource.increment_words_call_framed context selected entered workObject 512 192 6 (dropped old 192)
      (wellScoped_enter well) array (by norm_num) (by norm_num) (dropped_normalized digits)
    have zero : (FFT.Limbs.incrementDigits IncrementSource.base (fun k=>dropped old 192 (192+k)) 6).2=0:=increment_status_zero digits
    rw [zero] at called
    have frame:=ComplexSource.add_caller_frame fullFrame
    have oldParams:=params.enter
    have newParams : Locals middle name type ids owner (values workObject old 4):=by
      refine ⟨?_,?_,params.distinct,oldParams.bound.trans_le frame.frame.nextScope⟩
      · intro v;rw [frame.environment];exact oldParams.lookup v
      · intro v;exact ComplexSource.slot_after_call (wellScoped_enter well) (oldParams.slots v) frame (by simpa using (separate v).symm)
    have args : Args context entered arguments [.pointer (wordPointer workObject 192),.integer (integer64 6)] entered:=by
      refine .ordered (List.Perm.refl _) (.cons (.variable (oldParams.lookup Var.total) (oldParams.read Var.total))
        (.cons (.literal (.integer 6 "ULL") _ (.integer (integer64 6)) (by rfl)) .nil)) ?_
      exact .cons rfl (.cons rfl .nil)
    have statusSlot : Slot entered (ids Var.status) owner .u64 (.integer (integer64 0)):=oldParams.slots Var.status
    have newStatus : Slot middle (ids Var.status) owner .u64 (.integer (integer64 0)):=newParams.slots Var.status
    have statement : Exec context entered incrementStmt .normal middle:=
      StatusCall.assignment_execution (oldParams.lookup Var.status) (newParams.lookup Var.status) statusSlot newStatus args called
    let after : State F:={middle.leaveScope before.nextScope before.environment with scope:=before.scope}
    have block : Exec context before (.block [incrementStmt]) .normal after:=.block (by rfl) (.cons statement .nil) (by rfl)
    have run : Exec context before roundingBranch .normal after:=.ifTrue ev
      (by simp [Value.truth,Integer.truth,Integer.boolean,Integer.toInt,IntKind.signed,positive]) block
    have closed:=close_frame well (le_refl before.nextObject) frame.frame
    refine ⟨after,run,?_,?_,closed,?_⟩
    · simpa only [roundData,if_neg hz] using ComplexSource.word_array_leave rep before.nextScope before.scope before.environment
    · exact newParams.leave (by have b:=params.bound;omega) before.environment params.lookup before.scope
    · intro other flow arbitrary
      cases arbitrary with
      | ifFalse actual truth=>
        obtain ⟨rfl,rfl⟩:=PureDeterminism.eval_unique (by simp [roundingTest,SourcePure.CallFree]) ev actual
        simp [Value.truth,Integer.truth,Integer.boolean,Integer.toInt,IntKind.signed,positive] at truth
      | ifTrue actual truth body=>
        obtain ⟨rfl,rfl⟩:=PureDeterminism.eval_unique (by simp [roundingTest,SourcePure.CallFree]) ev actual
        cases body with
        | block enteredEq body finish=>
          subst_vars
          have everyStatement : ∀other flow,Exec context entered incrementStmt flow other → flow=.normal ∧ other=middle:=by
            intro other flow exec
            apply StatusCall.assignment_every_execution (oldParams.lookup Var.status) (newParams.lookup Var.status) statusSlot newStatus
              (by intro e member;simp only [arguments,List.mem_cons,List.mem_nil_iff,or_false] at member;rcases member with rfl|rfl <;> trivial)
              args ?_ exec
            intro other result run'
            exact IncrementSource.returned_call_unique selected called run'
          cases body with
          | abrupt actual abnormal=>exact False.elim (abnormal (everyStatement _ _ actual).1)
          | cons actual tail=>
            obtain ⟨_,eqs⟩:=everyStatement _ _ actual
            cases eqs
            cases tail
            exact ⟨rfl,rfl⟩

#print axioms rounding_execution
end RH080Next.FFTPV.DropTwoSource
