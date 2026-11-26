/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTAnswerHeader
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.AnswerSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings
open ApplicationBirthFrame

private theorem header_then_every {F : Type} {context : Context F} {before middle after other : State F}
    {a b c : Stmt} {flow : Flow}
    (header : ∀state flow,ExecList context before [a,b] flow state → flow=.normal ∧ state=middle)
    (last : ∀state flow,Exec context middle c flow state → flow=.normal ∧ state=after)
    (run : ExecList context before [a,b,c] flow other) : flow=.normal ∧ other=after := by
  cases run with
  | abrupt actual abnormal=>exact False.elim (abnormal (header _ _ (.abrupt actual abnormal)).1)
  | cons aRun tail=>
    cases tail with
    | abrupt actual abnormal=>exact False.elim (abnormal (header _ _ (.cons aRun (.abrupt actual abnormal))).1)
    | cons bRun tail=>
      obtain ⟨_,eqs⟩:=header _ _ (.cons aRun (.cons bRun .nil))
      cases eqs
      cases tail with
      | abrupt actual abnormal=>exact False.elim (abnormal (last _ _ actual).1)
      | cons actual tail=>
        obtain ⟨_,eqs⟩:=last _ _ actual
        cases eqs
        cases tail
        exact ⟨rfl,rfl⟩

/-- The actual outer status block performs both real conversion calls and
local births before its guarded additions. Its mathematical specification
includes the original failure sentinel; no favorable numerical result or
final PNT bound is a premise. -/
theorem status_execution {F : Type} (context : Context F)
    (selected : findFunction context.program "convert_bound"=some convert_bound_ast)
    (before : State F) (workObject owner prior allowance : Nat) (ids : MainVar→Nat) (data : Nat→Nat)
    (params : Locals before (fun v=>name (lift v)) (fun v=>type (lift v)) ids owner
      (fun v=>values workObject 0 0 prior (lift v)))
    (array : WordArrayRep before workObject 512 data) (separate : ∀v,workObject≠ids v) (well : WellScoped before)
    (priorFits : prior<2^64) (totalDigits : ∀k,k<6 → data (192+k)<1000000000)
    (quadDigits : ∀k,k<6 → data (208+k)<1000000000) (budget : allowance≤615) :
    ∃after,Exec context before (statusBranch allowance) .normal after ∧
      WordArrayRep after workObject 512 data ∧
      Locals after (fun v=>name (lift v)) (fun v=>type (lift v)) ids owner
        (fun v=>values workObject 0 0 (computed (firstValue data) (secondValue data) prior allowance) (lift v)) ∧
      Frame before.nextObject before after [ids MainVar.answer] ∧
      (∀other flow,Exec context before (statusBranch allowance) flow other → flow=.normal ∧ other=after) := by
  obtain ⟨headerState,firstId,secondId,headerRun,headerView,headerFrame,headerScope,headerEvery⟩:=
    header_execution context selected before.enterScope workObject owner prior ids data params.enter array separate (wellScoped_enter well) priorFits totalDigits quadDigits
  obtain ⟨middle,logicRun,post,logicFrame⟩:=logic_execution context headerView budget
  have logicOnly : SourceNoAlloc.Only (logic allowance):=by
    simp [logic,firstTest,innerBranch,secondTest,assignment,SourceNoAlloc.Only,SourcePure.CallFree]
  have effect:=SourceNoAlloc.exec_effect logicRun logicOnly headerView.well
  have enlarged : Frame before.nextObject before.enterScope headerState [ids MainVar.answer]:=by
    refine ⟨headerFrame.well,headerFrame.fresh,headerFrame.nextObject,headerFrame.nextScope,headerFrame.mode,headerFrame.foreign,?_⟩
    intro id old away
    exact headerFrame.outside id old (by simp)
  have tailFrame : Frame before.nextObject headerState middle [ids MainVar.answer]:=by
    refine ⟨effect.well,?_,?_,logicFrame.nextScope,logicFrame.mode,effect.foreign,?_⟩
    · rw [logicFrame.nextObject];exact headerFrame.fresh
    · rw [logicFrame.nextObject]
    · intro id old away
      exact logicFrame.outside id (by simpa only [combinedIds] using away)
  have closed:=close_frame well (le_refl before.nextObject) (enlarged.trans tailFrame)
  have runList : ExecList context before.enterScope [firstDeclaration,secondDeclaration,logic allowance] .normal middle := by
    cases headerRun with
    | abrupt _ bad=>exact False.elim (bad rfl)
    | cons aRun tail=>
      cases tail with
      | abrupt _ bad=>exact False.elim (bad rfl)
      | cons bRun tail=>cases tail;exact .cons aRun (.cons bRun (.cons logicRun .nil))
  let after : State F:={middle.leaveScope before.nextScope before.environment with scope:=before.scope}
  have test : Eval context before (.binary .eq (.variable "status") (.literal (.integer 0 "ULL"))) (.integer (.boolean true)) before:=
    .binaryLR (.variable (params.lookup MainVar.status) (params.read MainVar.status))
      (.literal (.integer 0 "ULL") _ (.integer (integer64 0)) (by rfl)) (by rfl)
  have block : Exec context before (.block [firstDeclaration,secondDeclaration,logic allowance]) .normal after:=.block (by rfl) runList (by rfl)
  have run : Exec context before (statusBranch allowance) .normal after:=.ifTrue test (by rfl) block
  have middleParams : Locals middle (fun v=>name (lift v)) (fun v=>type (lift v)) ids owner
      (fun v=>values workObject 0 0 (computed (firstValue data) (secondValue data) prior allowance) (lift v)):=by
    constructor
    · intro v;cases v <;> exact post.params.lookup _
    · intro v;cases v with
      | total=>exact post.params.slots Var.total
      | quad=>exact post.params.slots Var.quad
      | status=>exact post.params.slots Var.status
      | answer=>exact post.params.slots Var.answer
    · exact params.distinct
    · exact post.params.bound Var.answer
  have different : before.nextScope≠owner:=by have b:=params.bound;omega
  have projected := middleParams.leave different before.environment params.lookup before.scope
  refine ⟨after,run,ComplexSource.word_array_leave post.array before.nextScope before.scope before.environment,projected,closed,?_⟩
  intro other flow arbitrary
  cases arbitrary with
  | ifFalse actual truth=>
    obtain ⟨rfl,rfl⟩:=PureDeterminism.eval_unique (by trivial) test actual
    cases truth
  | ifTrue actual truth body=>
    obtain ⟨rfl,rfl⟩:=PureDeterminism.eval_unique (by trivial) test actual
    cases body with
    | block entered arbitrary finish=>
      subst_vars
      have lastEvery : ∀state flow,Exec context headerState (logic allowance) flow state → flow=.normal ∧ state=middle:=by
        intro state flow exec
        have eq:=logic_unique context allowance logicRun exec
        exact ⟨eq.1.symm,eq.2.symm⟩
      obtain ⟨eqf,eqs⟩:=header_then_every headerEvery lastEvery arbitrary
      exact ⟨eqf,by rw [eqs];rfl⟩

#print axioms status_execution
end RH080Next.FFTPV.AnswerSource
