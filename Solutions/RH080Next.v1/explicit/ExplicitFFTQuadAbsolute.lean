/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTQuadBirths
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 4096
namespace RH080Next.FFTPV.QuadSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings
open InputLoader RootSource

theorem aux_after_empty_frame {F : Type} {before after : State F} {workObject fo cutoff : Nat} {auxIds : Aux → Nat}
    (locals : Locals before auxName auxType auxIds fo (auxValues workObject)) (old : ∀v,auxIds v< cutoff)
    (frame : ApplicationBirthFrame.Frame cutoff before after []) (env : after.environment=before.environment) :
    Locals after auxName auxType auxIds fo (auxValues workObject):=
  ⟨by rw [env];exact locals.lookup,
    fun v=>⟨(locals.slots v).storable,(frame.outside _ (old v) (by simp)).trans (locals.slots v).object⟩,
    locals.distinct,locals.bound.trans_le frame.nextScope⟩

theorem absolute_branch_unique {F : Type} (context : Context F) : CompareSource.Unique context absoluteBranch:=by
  have positive : CompareSource.Unique context (.block [positiveAssignment]):=
    CompareSource.block_unique (by intro s hs;simp only [List.mem_singleton] at hs;subst s;exact fun a b=> PureDeterminism.simple_unique (by trivial) a b)
  have negative : CompareSource.Unique context (.block [negativeAssignment]):=
    CompareSource.block_unique (by intro s hs;simp only [List.mem_singleton] at hs;subst s;exact fun a b=> PureDeterminism.simple_unique (by trivial) a b)
  intro before a b fa fb first second
  cases first with
  | ifTrue ev truth run=>
    cases second with
    | ifTrue ev' truth' run'=>
      obtain ⟨rfl,rfl⟩:=PureDeterminism.eval_unique (by trivial) ev ev'
      exact positive run run'
    | ifElse ev' truth' run'=> cases (PureDeterminism.eval_unique (by trivial) ev ev').1;simp_all
  | ifElse ev truth run=>
    cases second with
    | ifTrue ev' truth' run'=> cases (PureDeterminism.eval_unique (by trivial) ev ev').1;simp_all
    | ifElse ev' truth' run'=>
      obtain ⟨rfl,rfl⟩:=PureDeterminism.eval_unique (by trivial) ev ev'
      exact negative run run'

theorem View.absolute_execution {F : Type} (context : Context F) {before : State F} {input : InputLoader.Input} {workObject fo bo j cutoff : Nat}
    {ids : InputLoader.Var → Nat} {auxIds : Aux → Nat} {dataMemory workData : Nat → Nat}
    (h : View before input workObject fo bo 2 j cutoff ids auxIds (plannedValues input j) dataMemory workData) :
    ∃after,Exec context before absoluteBranch .normal after ∧ Every context before absoluteBranch .normal after ∧
      View after input workObject fo bo 2 j cutoff ids auxIds (absoluteValues input j) dataMemory workData ∧
      ApplicationBirthFrame.Frame cutoff before after []:=by
  let encoded:=input.profile.encoded j
  have encoded64 : encoded<2^64:=lt_trans (input.profile.encoded_bound j h.body.active) (by norm_num [InputCell.scale])
  have scale64 : InputCell.scale<2^64:=by norm_num [InputCell.scale]
  have abs64 : coefficientAbs input.profile j<2^64:=lt_of_le_of_lt (coefficientAbs_bound input.profile j h.body.active) (by norm_num)
  have test : Eval context before magnitudeTest (.integer (.boolean (decide (InputCell.scale≤ encoded)))) before:=
    .binaryLR (h.body.variable context .e (by norm_num [Active,localIndex]))
      (.literal (.integer InputCell.scale "ULL") _ (.integer (integer64 InputCell.scale)) (by rfl))
      (by change Option.map Value.integer (Integer.binary .ge (integer64 encoded) (integer64 InputCell.scale))=_;rw [binary64_ge encoded InputCell.scale encoded64 scale64];rfl)
  let entry:=before.enterScope
  let expression : Expr:=if InputCell.scale≤ encoded then positiveExpression else negativeExpression
  have bindings:=h.body.bindings.enter
  have we : WellScoped entry:=wellScoped_enter h.body.well
  have eRead : Eval context entry (.variable "e") (.integer (integer64 encoded)) entry:=
    .variable (bindings.lookup (.inr .e) (by norm_num [Active,localIndex])) (bindings.read (.inr .e) (by norm_num [Active,localIndex]))
  have scaleRead : Eval context entry scaleLiteral (.integer (integer64 InputCell.scale)) entry:=.literal _ _ _ (by rfl)
  have evaluated : Eval context entry expression (.integer (integer64 (coefficientAbs input.profile j))) entry:=by
    by_cases positive : InputCell.scale≤ encoded
    · dsimp only [expression]
      rw [if_pos positive]
      apply Eval.paren
      apply Eval.binaryLR eRead scaleRead
      have absEq : coefficientAbs input.profile j=encoded-InputCell.scale:=by
        change (if InputCell.scale≤ encoded then encoded-InputCell.scale else InputCell.scale-encoded)=_
        rw [if_pos positive]
      rw [absEq]
      exact congrArg (Option.map Value.integer) (binary64_sub encoded InputCell.scale encoded64 scale64 positive)
    · dsimp only [expression]
      rw [if_neg positive]
      apply Eval.paren
      apply Eval.binaryLR scaleRead eRead
      have absEq : coefficientAbs input.profile j=InputCell.scale-encoded:=by
        change (if InputCell.scale≤ encoded then encoded-InputCell.scale else InputCell.scale-encoded)=_
        rw [if_neg positive]
      rw [absEq]
      exact congrArg (Option.map Value.integer) (binary64_sub InputCell.scale encoded scale64 encoded64 (show encoded≤ InputCell.scale by omega))
  have pure : SourcePure.CallFree expression:=by unfold expression;split_ifs <;> trivial
  obtain ⟨middle,assigned,everyAssigned,post,stored,frameInside⟩:=bindings.assign context we (.inr .value) (by norm_num [Active,localIndex])
    (.integer (integer64 (coefficientAbs input.profile j))) expression (ZeroFrame.u64_storable _ abs64) evaluated pure [] h.body.fresh
    (Or.inr (h.body.born .value (by norm_num [Active,localIndex])))
  let after : State F:={middle.leaveScope before.nextScope before.environment with scope:=before.scope}
  have run : Exec context before absoluteBranch .normal after:=by
    by_cases positive : InputCell.scale≤ encoded
    · have bodyRun : Exec context entry positiveAssignment .normal middle:=by simpa only [expression,if_pos positive,varName,temporaryName,positiveAssignment] using assigned
      exact .ifTrue test (by simp [Value.truth,Integer.truth,Integer.boolean,Integer.toInt,IntKind.signed,positive]) (.block (by rfl) (.cons bodyRun .nil) (by rfl))
    · have bodyRun : Exec context entry negativeAssignment .normal middle:=by simpa only [expression,if_neg positive,varName,temporaryName,negativeAssignment] using assigned
      exact .ifElse test (by simp [Value.truth,Integer.truth,Integer.boolean,Integer.toInt,IntKind.signed,positive]) (.block (by rfl) (.cons bodyRun .nil) (by rfl))
  have frame:=ApplicationBirthFrame.close_frame h.body.well h.body.fresh frameInside
  have dataEntry : WordArrayRep entry input.object (12*input.profile.grid) dataMemory:=h.body.array
  have workEntry : WordArrayRep entry workObject 512 workData:=h.work
  have dataMiddle:=ProductInner.array_store_old dataEntry (h.body.separate (.inr .value) (by norm_num [Active,localIndex])) stored
  have workMiddle:=ProductInner.array_store_old workEntry (h.workSeparate (.inr .value) (by norm_num [Active,localIndex])) stored
  have different (v : InputLoader.Var) (hv : Active 2 v) : before.nextScope≠owner fo bo v:=by have b:=h.body.bindings.bound v hv;omega
  have finalBindings:=post.leave (restore:=before.scope) different before.environment h.body.bindings.lookup
  have body : BodyView after input fo bo 2 j cutoff ids (absoluteValues input j) dataMemory:=
    ⟨IncrementSource.wordArray_leave dataMiddle,finalBindings,(by intro p;simp [absoluteValues,plannedValues]),h.body.separate,
      frame.well,h.body.scope,h.body.active,frame.fresh,h.body.born⟩
  have aux:=aux_after_empty_frame h.aux h.auxOld frame (by rfl)
  exact ⟨after,run,every_of_unique (absolute_branch_unique context) run,
    ⟨body,aux,IncrementSource.wordArray_leave workMiddle,h.different,h.workSeparate,h.auxSeparate,h.auxOld,h.cross,h.quadDigits,h.quadValue⟩,frame⟩

#print axioms View.absolute_execution
end RH080Next.FFTPV.QuadSource
