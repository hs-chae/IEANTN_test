/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTInputLoaderPartialAssign
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.InputLoader
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings
open RootSource

def scaleLiteral : Expr:=.literal (.integer InputCell.scale "ULL")
def magnitudeTest : Expr:=.binary .ge (.variable "e") scaleLiteral

def positiveExpression : Expr:=.paren (.binary .sub (.variable "e") scaleLiteral)
def negativeExpression : Expr:=.paren (.binary .sub scaleLiteral (.variable "e"))
def positiveAssignment : Stmt:=.assign (.variable "value") positiveExpression
def negativeAssignment : Stmt:=.assign (.variable "value") negativeExpression
def signAssignment : Stmt:=.assign (.variable "sign") (.literal (.integer 1 "ULL"))
def magnitudeBranch : Stmt:=.ite magnitudeTest (.block [positiveAssignment]) (some (.block [negativeAssignment,signAssignment]))

def branchValues (input : Input) (j : Nat) : Var → Value:=
  Function.update (Function.update (plannedValues input j) (.inr .value)
    (.integer (integer64 (InputCell.magnitudeValue (input.profile.encoded j))))) (.inr .sign)
    (.integer (integer64 (InputCell.signValue (input.profile.encoded j))))

theorem source_branch : (ProductRow.items loopBody)[3]?=some magnitudeBranch:=rfl

theorem magnitude_branch_unique {F : Type} (context : Context F) : CompareSource.Unique context magnitudeBranch:=by
  have positiveUnique : CompareSource.Unique context (.block [positiveAssignment]):=
    CompareSource.block_unique (by intro s hs;simp only [List.mem_singleton] at hs;subst s;exact fun a b=> PureDeterminism.simple_unique (by trivial) a b)
  have negativeUnique : CompareSource.Unique context (.block [negativeAssignment,signAssignment]):=by
    apply CompareSource.block_unique
    intro s hs;simp only [List.mem_cons,List.mem_nil_iff,or_false] at hs
    rcases hs with rfl|rfl
    all_goals exact fun a b=> PureDeterminism.simple_unique (by trivial) a b
  intro before a b fa fb first second
  cases first with
  | ifTrue ev truth run=>
    cases second with
    | ifTrue ev' truth' run'=>
      obtain ⟨rfl,rfl⟩:=PureDeterminism.eval_unique (by trivial) ev ev'
      exact positiveUnique run run'
    | ifElse ev' truth' run'=> cases (PureDeterminism.eval_unique (by trivial) ev ev').1;simp_all
  | ifElse ev truth run=>
    cases second with
    | ifTrue ev' truth' run'=> cases (PureDeterminism.eval_unique (by trivial) ev ev').1;simp_all
    | ifElse ev' truth' run'=>
      obtain ⟨rfl,rfl⟩:=PureDeterminism.eval_unique (by trivial) ev ev'
      exact negativeUnique run run'

theorem BodyView.magnitude_branch_execution {F : Type} (context : Context F) {before : State F} {input : Input} {fo bo j cutoff : Nat}
    {ids : Var → Nat} {memory : Nat → Nat}
    (h : BodyView before input fo bo 3 j cutoff ids (plannedValues input j) memory) :
    ∃after,Exec context before magnitudeBranch .normal after ∧ Every context before magnitudeBranch .normal after ∧
      BodyView after input fo bo 3 j cutoff ids (branchValues input j) memory ∧
      ApplicationBirthFrame.Frame cutoff before after []:=by
  let encoded:=input.profile.encoded j
  have encoded64 : encoded<2^64:=lt_trans (input.profile.encoded_bound j h.active) (by norm_num [InputCell.scale])
  have scale64 : InputCell.scale<2^64:=by norm_num [InputCell.scale]
  have abs64 : InputCell.magnitudeValue encoded<2^64:=
    lt_of_le_of_lt (InputCell.magnitude_value_bound encoded (input.profile.encoded_bound j h.active).le) scale64
  have conditionEval : Eval context before magnitudeTest (.integer (.boolean (decide (InputCell.scale≤ encoded)))) before:=
    .binaryLR (h.variable context .e (by norm_num [Active,localIndex])) (.literal (.integer InputCell.scale "ULL") _ (.integer (integer64 InputCell.scale)) (by rfl))
      (by change Option.map Value.integer (Integer.binary .ge (integer64 encoded) (integer64 InputCell.scale))=_;rw [binary64_ge encoded InputCell.scale encoded64 scale64];rfl)
  let entry:=before.enterScope
  have entered:=h.bindings.enter
  have we : WellScoped entry:=wellScoped_enter h.well
  have arrayEntry : WordArrayRep entry input.object (12*input.profile.grid) memory:=h.array
  have eRead : Eval context entry (.variable "e") (.integer (integer64 encoded)) entry:=
    .variable (entered.lookup (.inr .e) (by norm_num [Active,localIndex])) (entered.read (.inr .e) (by norm_num [Active,localIndex]))
  have literalEval : Eval context entry scaleLiteral (.integer (integer64 InputCell.scale)) entry:=.literal _ _ _ (by rfl)
  have bornValue:=h.born .value (by norm_num [Active,localIndex])
  have bornSign:=h.born .sign (by norm_num [Active,localIndex])
  have fresh : cutoff≤ entry.nextObject:=h.fresh
  have different (v : Var) (hv : Active 3 v) : before.nextScope≠owner fo bo v:=by
    have hb:=h.bindings.bound v hv;omega
  by_cases positive : InputCell.scale≤ encoded
  · have read : Eval context entry positiveExpression (.integer (integer64 (InputCell.magnitudeValue encoded))) entry:=by
      apply Eval.paren
      apply Eval.binaryLR eRead literalEval
      simpa only [binary,InputCell.magnitudeValue,if_pos positive,Option.map_some] using congrArg (Option.map Value.integer) (binary64_sub encoded InputCell.scale encoded64 scale64 positive)
    obtain ⟨middle,assigned,everyAssigned,post,stored,frameInside⟩:=entered.assign context we (.inr .value) (by norm_num [Active,localIndex])
      (.integer (integer64 (InputCell.magnitudeValue encoded))) positiveExpression (ZeroFrame.u64_storable _ abs64) read (by trivial) [] fresh (Or.inr bornValue)
    let after : State F:={middle.leaveScope before.nextScope before.environment with scope:=before.scope}
    have run : Exec context before magnitudeBranch .normal after:=.ifTrue conditionEval
      (by simp [Value.truth,Integer.truth,Integer.boolean,Integer.toInt,IntKind.signed,positive]) (.block (by rfl) (.cons assigned .nil) (by rfl))
    have frame:=ApplicationBirthFrame.close_frame h.well h.fresh frameInside
    have arrayMiddle:=ProductInner.array_store_old arrayEntry (h.separate (.inr .value) (by norm_num [Active,localIndex])) stored
    have same : Function.update (plannedValues input j) (.inr .value) (.integer (integer64 (InputCell.magnitudeValue encoded)))=branchValues input j:=by
      funext v;cases v with
      | inl p=> rfl
      | inr t=> cases t <;> simp [branchValues,plannedValues,InputCell.signValue,positive,encoded]
    rw [same] at post
    have bindings:=post.leave (restore:=before.scope) different before.environment h.bindings.lookup
    refine ⟨after,run,every_of_unique (magnitude_branch_unique context) run,
      ⟨IncrementSource.wordArray_leave arrayMiddle,bindings,?_,h.separate,frame.well,h.scope,h.active,frame.fresh,h.born⟩,frame⟩
    intro p;simp [branchValues,plannedValues]
  · have reverse : encoded≤ InputCell.scale:=by omega
    have read : Eval context entry negativeExpression (.integer (integer64 (InputCell.magnitudeValue encoded))) entry:=by
      apply Eval.paren
      apply Eval.binaryLR literalEval eRead
      simpa only [binary,InputCell.magnitudeValue,if_neg positive,Option.map_some] using congrArg (Option.map Value.integer) (binary64_sub InputCell.scale encoded scale64 encoded64 reverse)
    obtain ⟨middle,assigned,everyAssigned,post,stored,frame1⟩:=entered.assign context we (.inr .value) (by norm_num [Active,localIndex])
      (.integer (integer64 (InputCell.magnitudeValue encoded))) negativeExpression (ZeroFrame.u64_storable _ abs64) read (by trivial) [] fresh (Or.inr bornValue)
    have arrayMiddle:=ProductInner.array_store_old arrayEntry (h.separate (.inr .value) (by norm_num [Active,localIndex])) stored
    obtain ⟨finished,signRun,everySign,last,signStored,frame2⟩:=post.assign context frame1.well (.inr .sign) (by norm_num [Active,localIndex])
      (.integer (integer64 1)) (.literal (.integer 1 "ULL")) (ZeroFrame.u64_storable 1 (by norm_num)) (.literal _ _ _ (by rfl)) (by trivial) [] frame1.fresh (Or.inr bornSign)
    have arrayFinished:=ProductInner.array_store_old arrayMiddle (h.separate (.inr .sign) (by norm_num [Active,localIndex])) signStored
    let after : State F:={finished.leaveScope before.nextScope before.environment with scope:=before.scope}
    have run : Exec context before magnitudeBranch .normal after:=.ifElse conditionEval
      (by simp [Value.truth,Integer.truth,Integer.boolean,Integer.toInt,IntKind.signed,positive]) (.block (by rfl) (.cons assigned (.cons signRun .nil)) (by rfl))
    have frame:=ApplicationBirthFrame.close_frame h.well h.fresh (frame1.trans frame2)
    have same : Function.update (Function.update (plannedValues input j) (.inr .value) (.integer (integer64 (InputCell.magnitudeValue encoded)))) (.inr .sign) (.integer (integer64 1))=branchValues input j:=by
      simp only [branchValues,InputCell.signValue,if_neg positive,encoded]
    rw [same] at last
    have bindings:=last.leave (restore:=before.scope) different before.environment h.bindings.lookup
    refine ⟨after,run,every_of_unique (magnitude_branch_unique context) run,
      ⟨IncrementSource.wordArray_leave arrayFinished,bindings,?_,h.separate,frame.well,h.scope,h.active,frame.fresh,h.born⟩,frame⟩
    intro p;simp [branchValues,plannedValues]

#print axioms BodyView.magnitude_branch_execution
end RH080Next.FFTPV.InputLoader
