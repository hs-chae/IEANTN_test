/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTInputLoaderCanonical
import FFTRecursiveCopyFrame
import FFTCopyDeterminism
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.InputLoader
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings
open RootSource

def mirrorPointer : Expr:=.paren (.binary .add (.variable "data")
  (.paren (.binary .mul (.paren (.binary .sub (.variable "n") (.variable "j"))) (.literal (.integer 12 "ULL")))))
def copyStatement : Stmt:=.expression (.call "copy_words" [mirrorPointer,.variable "p",.literal (.integer 12 "ULL")])
def mirrorCondition : Expr:=.binary .gt (.variable "j") (.literal (.integer 0 "ULL"))
def mirrorStatement : Stmt:=.ite mirrorCondition (.block [copyStatement]) none

theorem source_mirror : (ProductRow.items loopBody)[12]?=some mirrorStatement:=rfl

theorem Profile.copy_selected {F : Type} (p : Profile) (context : Context F) (pinned : context.program=p.program) :
    findFunction context.program "copy_words"=some copy_words_ast:=by rw [pinned];cases p <;> rfl

theorem every_if_true {F : Type} {context : Context F} {before after : State F} {condition : Expr} {value : Value} {body : Stmt}
    (pure : SourcePure.CallFree condition) (eval : Eval context before condition value before) (truth : value.truth=some true)
    (known : Every context before body .normal after) : Every context before (.ite condition body none) .normal after:=by
  intro other flow run
  cases run with
  | ifTrue actual test bodyRun=>
    obtain ⟨rfl,rfl⟩:=PureDeterminism.eval_unique pure eval actual
    exact known _ _ bodyRun
  | ifFalse actual test=>
    obtain ⟨rfl,rfl⟩:=PureDeterminism.eval_unique pure eval actual
    cases truth.symm.trans test

theorem every_if_false {F : Type} {context : Context F} {before : State F} {condition : Expr} {value : Value} {body : Stmt}
    (pure : SourcePure.CallFree condition) (eval : Eval context before condition value before) (truth : value.truth=some false) :
    Every context before (.ite condition body none) .normal before:=by
  intro other flow run
  cases run with
  | ifTrue actual test bodyRun=>
    obtain ⟨rfl,rfl⟩:=PureDeterminism.eval_unique pure eval actual
    cases truth.symm.trans test
  | ifFalse actual test=>
    obtain ⟨rfl,rfl⟩:=PureDeterminism.eval_unique pure eval actual
    exact ⟨rfl,rfl⟩

theorem BodyView.mirror_execution {F : Type} (context : Context F) {before : State F} {input : Input} {fo bo j cutoff : Nat}
    {ids : Var → Nat} {memory : Nat → Nat}
    (h : BodyView before input fo bo 5 j cutoff ids (dividedValues input j) (readyCell memory (12*j) (input.profile.encoded j)))
    (pinned : context.program=input.profile.program) :
    ∃after,Exec context before mirrorStatement .normal after ∧ Every context before mirrorStatement .normal after ∧
      BodyView after input fo bo 5 j cutoff ids (dividedValues input j) (iterationData memory input.profile.grid j (input.profile.encoded j)) ∧
      ApplicationBirthFrame.Frame cutoff before after [input.object]:=by
  have shape:=input.profile.shape
  have j64 : j<2^64:=by have a:=h.active;omega
  have n64 : input.profile.grid<2^64:=by omega
  have test : Eval context before mirrorCondition (.integer (.boolean (decide (0< j)))) before:=
    .binaryLR (h.parameter_eval context .j) (.literal (.integer 0 "ULL") _ (.integer (integer64 0)) (by rfl))
      (by simp only [parameterValues,binary,CompareSource.binary64_gt j 0 j64 (show 0<2^64 by norm_num),Option.map_some])
  by_cases positive : 0< j
  · let entry:=before.enterScope
    have entered:=h.bindings.enter
    have we : WellScoped entry:=wellScoped_enter h.well
    have arrayEntry : WordArrayRep entry input.object (12*input.profile.grid) (readyCell memory (12*j) (input.profile.encoded j)):=h.array
    have nRead : Eval context entry (.variable "n") (.integer (integer64 input.profile.grid)) entry:=by
      simpa [varName,parameterName,dividedValues,branchValues,plannedValues,parameterValues] using
        Eval.variable (context:=context) (entered.lookup (.inl .n) (by trivial)) (entered.read (.inl .n) (by trivial))
    have jRead : Eval context entry (.variable "j") (.integer (integer64 j)) entry:=by
      simpa [varName,parameterName,dividedValues,branchValues,plannedValues,parameterValues] using
        Eval.variable (context:=context) (entered.lookup (.inl .j) (by trivial)) (entered.read (.inl .j) (by trivial))
    have dataRead : Eval context entry (.variable "data") (.pointer (wordPointer input.object 0)) entry:=by
      simpa [varName,parameterName,dividedValues,branchValues,plannedValues,parameterValues] using
        Eval.variable (context:=context) (entered.lookup (.inl .data) (by trivial)) (entered.read (.inl .data) (by trivial))
    have pRead : Eval context entry (.variable "p") (.pointer (wordPointer input.object (12*j))) entry:=by
      simpa [varName,temporaryName,dividedValues,branchValues,plannedValues] using
        Eval.variable (context:=context) (entered.lookup (.inr .p) (by norm_num [Active,localIndex])) (entered.read (.inr .p) (by norm_num [Active,localIndex]))
    have sub64 : input.profile.grid-j<2^64:=lt_of_le_of_lt (Nat.sub_le _ _) n64
    have index64 : (input.profile.grid-j)*12<2^64:=by omega
    have subRead : Eval context entry (.paren (.binary .sub (.variable "n") (.variable "j"))) (.integer (integer64 (input.profile.grid-j))) entry:=
      .paren (.binaryLR nRead jRead (by simp only [binary,binary64_sub _ _ n64 j64 (show j≤ input.profile.grid by have a:=h.active;omega),Option.map_some]))
    have indexRead : Eval context entry (.paren (.binary .mul (.paren (.binary .sub (.variable "n") (.variable "j"))) (.literal (.integer 12 "ULL"))))
        (.integer (integer64 ((input.profile.grid-j)*12))) entry:=
      .paren (.binaryLR subRead (.literal (.integer 12 "ULL") _ (.integer (integer64 12)) (by rfl))
        (by simp only [binary,binary64_mul _ _ sub64 (show 12<2^64 by norm_num) index64,Option.map_some]))
    have offsetBound : 0+(input.profile.grid-j)*12<12*input.profile.grid:=by omega
    have added:=slice_pointer_add (start:=0) (i:=(input.profile.grid-j)*12) arrayEntry offsetBound
    have outRead : Eval context entry mirrorPointer (.pointer (wordPointer input.object (12*(input.profile.grid-j)))) entry:=by
      apply Eval.paren
      apply Eval.binaryLR dataRead indexRead
      simpa only [binary,Option.map_some,Nat.zero_add,Nat.mul_comm] using congrArg (Option.map Value.pointer) added
    have selected:=input.profile.copy_selected context pinned
    obtain ⟨middle,called,array,sourceRead,frame,birth⟩:=CopyLoop.copy_words_call_framed context selected entry
      input.object (12*input.profile.grid) (12*(input.profile.grid-j)) input.object (12*input.profile.grid) (12*j) 12 _ _ we arrayEntry arrayEntry
      (fun _=> rfl) (Or.inr (Or.inr (Or.inr (by have a:=h.active;omega)))) (by omega) (by have a:=h.active;omega) (by norm_num)
    have args : Args context entry [mirrorPointer,.variable "p",.literal (.integer 12 "ULL")]
        [.pointer (wordPointer input.object (12*(input.profile.grid-j))),.pointer (wordPointer input.object (12*j)),.integer (integer64 12)] entry:=by
      apply Args.ordered (order:=[(0,mirrorPointer),(1,.variable "p"),(2,.literal (.integer 12 "ULL"))])
        (evaluated:=[(0,.pointer (wordPointer input.object (12*(input.profile.grid-j)))),(1,.pointer (wordPointer input.object (12*j))),(2,.integer (integer64 12))])
      · exact List.Perm.refl _
      · exact .cons outRead (.cons pRead (.cons (.literal _ _ _ (by rfl)) .nil))
      · change List.Forall₂ _ [0,1,2] _;exact .cons rfl (.cons rfl (.cons rfl .nil))
    have callRun : Exec context entry copyStatement .normal middle:=.expression (.call args called)
    have callEvery:=every_expression_call (by intro e he;simp only [List.mem_cons,List.mem_nil_iff,or_false] at he;rcases he with rfl|rfl|rfl <;> trivial) args
      (fun state result actual=> CopyLoop.call_unique selected called actual)
    let after : State F:={middle.leaveScope before.nextScope before.environment with scope:=before.scope}
    have blockEvery : Every context before (.block [copyStatement]) .normal after:=every_block (every_cons callEvery (every_nil middle))
    have run : Exec context before mirrorStatement .normal after:=.ifTrue test
      (by simp [Value.truth,Integer.truth,Integer.boolean,Integer.toInt,IntKind.signed,positive]) (.block (by rfl) (.cons callRun .nil) (by rfl))
    have caller : MultiplyCall.CallerFrame entry middle [input.object]:=⟨frame.environment,frame.scope,birth⟩
    have boundBindings:=entered.after_call we caller (by intro v hv;simp only [List.mem_singleton];exact (h.separate v hv).symm)
    have different (v : Var) (hv : Active 5 v) : before.nextScope≠owner fo bo v:=by have b:=h.bindings.bound v hv;omega
    have finalBindings:=boundBindings.leave (restore:=before.scope) different before.environment h.bindings.lookup
    have finalArray : WordArrayRep after input.object (12*input.profile.grid) (iterationData memory input.profile.grid j (input.profile.encoded j)):=by
      simpa only [iterationData,if_pos positive] using IncrementSource.wordArray_leave array
    have full:=ApplicationBirthFrame.close_frame h.well h.fresh (lower_frame birth h.fresh)
    exact ⟨after,run,every_if_true (by trivial) test (by simp [Value.truth,Integer.truth,Integer.boolean,Integer.toInt,IntKind.signed,positive]) blockEvery,
      ⟨finalArray,finalBindings,h.parameters,h.separate,full.well,h.scope,h.active,full.fresh,h.born⟩,full⟩
  · have run : Exec context before mirrorStatement .normal before:=.ifFalse test (by simp [Value.truth,Integer.truth,Integer.boolean,Integer.toInt,IntKind.signed,positive])
    exact ⟨before,run,every_if_false (by trivial) test (by simp [Value.truth,Integer.truth,Integer.boolean,Integer.toInt,IntKind.signed,positive]),
      by simpa only [iterationData,if_neg positive] using h,ApplicationBirthFrame.Frame.refl _ _ h.well h.fresh⟩

#print axioms BodyView.mirror_execution
end RH080Next.FFTPV.InputLoader
