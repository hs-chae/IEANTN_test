/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTAnswerBase
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.AnswerSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings

theorem assignment_execution {F : Type} (context : Context F) {before : State F}
    {workObject first second answer allowance : Nat} {ids owners : Var→Nat} {data : Nat→Nat}
    (h : View before workObject ids owners first second answer data)
    (outer : first<limit) (inner : second<limit-first) (budget : allowance≤615) :
    ∃after,Exec context before (assignment allowance) .normal after ∧
      View after workObject ids owners first second (first+second+allowance) data ∧
      ScanFrame.Frame before after [ids Var.answer] := by
  have sumFits : first+second<2^64:=by dsimp [limit] at outer inner;omega
  have finalFits : first+second+allowance<2^64:=by dsimp [limit] at outer inner;omega
  obtain ⟨after,written⟩:=ProductInner.slot_store_exists (h.params.slots Var.answer)
    (.integer (integer64 (first+second+allowance))) (ZeroFrame.u64_storable _ finalFits)
  have firstSum : Eval context before (.paren (.binary .add (.variable "first") (.variable "second")))
      (.integer (integer64 (first+second))) before:=
    .paren (.binaryLR (.variable (h.params.lookup Var.first) (h.params.read Var.first))
      (.variable (h.params.lookup Var.second) (h.params.read Var.second))
      (by simp only [values,binary,binary64_add first second h.firstFits h.secondFits sumFits,Option.map_some]))
  have total : Eval context before (.paren (.binary .add (.paren (.binary .add (.variable "first") (.variable "second"))) (.literal (.integer allowance "ULL"))))
      (.integer (integer64 (first+second+allowance))) before:=
    .paren (.binaryLR firstSum (.literal (.integer allowance "ULL") _ (.integer (integer64 allowance)) (by simp [Literal.value,integer64];omega))
      (by simp only [binary,binary64_add (first+second) allowance sumFits (by omega) finalFits,Option.map_some]))
  have run : Exec context before (assignment allowance) .normal after:=.assign total (.variable (h.params.lookup Var.answer)) written
  have params:=h.params.store Var.answer (.integer (integer64 (first+second+allowance))) (ZeroFrame.u64_storable _ finalFits) written
  have eq : Function.update (values workObject first second answer) Var.answer (.integer (integer64 (first+second+allowance)))=
      values workObject first second (first+second+allowance):=by funext v;cases v <;> simp [values,Function.update]
  rw [eq] at params
  have fields:=SourceLocals.store_frame written
  have array : WordArrayRep after workObject 512 data:=
    ⟨fields.2.1.trans h.array.1,(fields.2.2.2.2.2 workObject (h.separate Var.answer)).trans h.array.2.1,h.array.2.2⟩
  exact ⟨after,run,⟨params,array,h.separate,h.firstFits,h.secondFits,finalFits,wellScoped_store h.well written⟩,
    ScanFrame.Frame.store (by simp [scalarPointer]) written⟩

private theorem close_view {F : Type} {context : Context F} {before middle : State F}
    {workObject first second answer result : Nat} {ids owners : Var→Nat} {data : Nat→Nat}
    {body : List Stmt} (h : View before workObject ids owners first second answer data)
    (post : View middle workObject ids owners first second result data)
    (run : ExecList context before.enterScope body .normal middle)
    (pure : SourceNoAlloc.Only (.block body)) :
    View {middle.leaveScope before.nextScope before.environment with scope:=before.scope} workObject ids owners first second result data := by
  have execution : Exec context before (.block body) .normal {middle.leaveScope before.nextScope before.environment with scope:=before.scope}:=
    .block (by rfl) run (by rfl)
  have effect:=SourceNoAlloc.exec_effect execution pure h.well
  exact ⟨post.params.leave (fun v=>by have b:=h.params.bound v;omega) before.environment h.params.lookup,
    ComplexSource.word_array_leave post.array before.nextScope before.scope before.environment,
    post.separate,post.firstFits,post.secondFits,post.answerFits,effect.well⟩

theorem inner_execution {F : Type} (context : Context F) {before : State F}
    {workObject first second answer allowance : Nat} {ids owners : Var→Nat} {data : Nat→Nat}
    (h : View before workObject ids owners first second answer data) (outer : first<limit) (budget : allowance≤615) :
    ∃after,Exec context before (innerBranch allowance) .normal after ∧
      View after workObject ids owners first second (if second<limit-first then first+second+allowance else answer) data ∧
      ScanFrame.Frame before after [ids Var.answer] := by
  by_cases inner : second<limit-first
  · obtain ⟨middle,assignment,post,frame⟩:=assignment_execution context h.enter outer inner budget
    have runList : ExecList context before.enterScope [AnswerSource.assignment allowance] .normal middle:=.cons assignment .nil
    let after : State F:={middle.leaveScope before.nextScope before.environment with scope:=before.scope}
    have block : Exec context before (.block [AnswerSource.assignment allowance]) .normal after:=.block (by rfl) runList (by rfl)
    have run : Exec context before (innerBranch allowance) .normal after:=.ifTrue (second_test context h outer)
      (by simp [Value.truth,Integer.truth,Integer.boolean,Integer.toInt,IntKind.signed,inner]) block
    refine ⟨after,run,?_,ScanFrame.Frame.close h.well frame⟩
    simpa only [if_pos inner] using close_view h post runList (by simp [AnswerSource.assignment,SourceNoAlloc.Only,SourcePure.CallFree])
  · exact ⟨before,.ifFalse (second_test context h outer) (by simp [Value.truth,Integer.truth,Integer.boolean,Integer.toInt,IntKind.signed,inner]),
      by simpa only [if_neg inner] using h,ScanFrame.Frame.refl before _⟩

theorem logic_execution {F : Type} (context : Context F) {before : State F}
    {workObject first second answer allowance : Nat} {ids owners : Var→Nat} {data : Nat→Nat}
    (h : View before workObject ids owners first second answer data) (budget : allowance≤615) :
    ∃after,Exec context before (logic allowance) .normal after ∧
      View after workObject ids owners first second (computed first second answer allowance) data ∧
      ScanFrame.Frame before after [ids Var.answer] := by
  by_cases outer : first<limit
  · obtain ⟨middle,inner,post,frame⟩:=inner_execution context h.enter outer budget
    have runList : ExecList context before.enterScope [innerBranch allowance] .normal middle:=.cons inner .nil
    let after : State F:={middle.leaveScope before.nextScope before.environment with scope:=before.scope}
    have block : Exec context before (.block [innerBranch allowance]) .normal after:=.block (by rfl) runList (by rfl)
    have run : Exec context before (logic allowance) .normal after:=.ifTrue (first_test context h)
      (by simp [Value.truth,Integer.truth,Integer.boolean,Integer.toInt,IntKind.signed,outer]) block
    refine ⟨after,run,?_,ScanFrame.Frame.close h.well frame⟩
    simpa only [computed,if_pos outer] using close_view h post runList (by simp [innerBranch,secondTest,assignment,SourceNoAlloc.Only,SourcePure.CallFree])
  · exact ⟨before,.ifFalse (first_test context h) (by simp [Value.truth,Integer.truth,Integer.boolean,Integer.toInt,IntKind.signed,outer]),
      by simpa only [computed,if_neg outer] using h,ScanFrame.Frame.refl before _⟩

theorem logic_unique {F : Type} (context : Context F) (allowance : Nat) : CompareSource.Unique context (logic allowance):=by
  apply DivideSource.if_unique firstTest (.block [innerBranch allowance]) (by simp [firstTest,SourcePure.CallFree])
  apply CompareSource.block_unique
  intro stmt member
  simp only [List.mem_singleton] at member
  subst stmt
  apply DivideSource.if_unique secondTest (.block [assignment allowance]) (by simp [secondTest,SourcePure.CallFree])
  apply CompareSource.block_unique
  intro stmt member
  simp only [List.mem_singleton] at member
  subst stmt
  exact fun first second=>PureDeterminism.simple_unique (by simp [assignment,PureDeterminism.Simple,SourcePure.CallFree]) first second

#print axioms assignment_execution
#print axioms logic_execution
#print axioms logic_unique
end RH080Next.FFTPV.AnswerSource
