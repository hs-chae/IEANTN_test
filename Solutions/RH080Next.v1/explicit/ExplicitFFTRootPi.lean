/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTRootBase
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.RootSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings
open IncrementSource (base)

def zeroStatement : Stmt:=.expression (.call "zero_words" [.variable "work",.literal (.integer 80 "ULL")])
def piStatement (j : Nat) : Stmt:=.assign (.index (.variable "work") (.literal (.integer j "ULL")))
  (.literal (.integer (piDigit j) "ULL"))
def piStatements (j : Nat) : List Stmt:=(List.range j).map piStatement

def prefixStatements : List Stmt:=zeroStatement::piStatements 5

def remainingStatements : List Stmt:=match initialize_root_ast.body with
  | .block body=>body.drop 6
  | _=>[]

/-- Exact prefix agreement with the independently source-linked AST. -/
theorem actual_prefix : initialize_root_ast.body=.block (prefixStatements++remainingStatements):=by rfl

theorem ParamView.reframe {F : Type} {before after : State F} {input : Input} {owner : Nat}
    {ids : Param → Nat} {old data : Nat → Nat} (h : ParamView before input owner ids old)
    (rep : WordArrayRep after input.layout.object input.layout.size data)
    (environment : after.environment=before.environment) (scope : before.scope=owner)
    (restore : after.scope=before.scope) (well : WellScoped after)
    (objects : ∀id,id<before.nextObject → id≠input.layout.object → after.objects id=before.objects id) :
    ParamView after input owner ids data := by
  refine ⟨rep,⟨?_,?_,h.locals.distinct,?_⟩,h.separate,well⟩
  · rw [environment]; exact h.locals.lookup
  · intro v
    refine ⟨(h.locals.slots v).storable,?_⟩
    rw [objects _ (h.well.objectIds _ _ (h.locals.slots v).object) (h.separate v).symm]
    exact (h.locals.slots v).object
  · rw [←scope,←restore]; exact well.current

/-- Actual zero_words call resets only the work slice of the caller's existing
allocation; root storage outside that slice is preserved by the exact data map. -/
theorem zero_execution {F : Type} (context : Context F)
    (selected : findFunction context.program "zero_words"=some zero_words_ast)
    {before : State F} {input : Input} {owner : Nat} {ids : Param → Nat}
    (h : ParamView before input owner ids input.old) (scope : before.scope=owner) :
    ∃after,Exec context before zeroStatement .normal after ∧
      ParamView after input owner ids (piData input.old input.layout.workStart 0) ∧ after.scope=owner := by
  obtain ⟨after,called,rep,frame⟩:=ZeroSlice.zero_words_call context selected before
    input.layout.object input.layout.size input.layout.workStart 80 input.old h.well h.array
    input.layout.workBound (by norm_num)
  have args : Args context before [.variable "work",.literal (.integer 80 "ULL")]
      [.pointer (wordPointer input.layout.object input.layout.workStart),.integer (integer64 80)] before := by
    apply Args.ordered (order:=[(0,.variable "work"),(1,.literal (.integer 80 "ULL"))])
      (evaluated:=[(0,.pointer (wordPointer input.layout.object input.layout.workStart)),(1,.integer (integer64 80))])
    · exact List.Perm.refl _
    · exact .cons (.variable (h.locals.lookup Param.work) (h.locals.read Param.work))
        (.cons (.literal (.integer 80 "ULL") _ (.integer (integer64 80)) (by rfl)) .nil)
    · change List.Forall₂ _ [0,1] _; exact .cons rfl (.cons rfl .nil)
  exact ⟨after,.expression (.call args called),h.reframe rep frame.environment scope frame.scope frame.well frame.objects,
    frame.scope.trans scope⟩

theorem pi_store_execution {F : Type} (context : Context F) {before : State F} {input : Input}
    {owner j : Nat} {ids : Param → Nat} (h : ParamView before input owner ids (piData input.old input.layout.workStart j))
    (hj : j<5) :
    ∃after,Exec context before (piStatement j) .normal after ∧
      ParamView after input owner ids (piData input.old input.layout.workStart (j+1)) ∧ after.scope=before.scope := by
  have hi : input.layout.workStart+j < input.layout.size:=by have hb:=input.layout.workBound;omega
  have j64 : j<2^64:=by omega
  have value64 : piDigit j<2^64:=lt_trans (piDigit_bound j) (by norm_num [base])
  obtain ⟨after,stored,rep⟩:=word_store_with_rep h.array hi value64
  have run : Exec context before (piStatement j) .normal after:=.assign
    (.literal (.integer (piDigit j) "ULL") _ (.integer (integer64 (piDigit j))) (by have hv : piDigit j<18446744073709551616:=value64;simp [Literal.value,integer64,hv]))
    (.index (.variable (h.locals.lookup Param.work) (h.locals.read Param.work))
      (.literal (.integer j "ULL") _ (.integer (integer64 j)) (by have hv : j<18446744073709551616:=j64;simp [Literal.value,integer64,hv]))
      (slice_pointer_add h.array hi)) stored
  have lm:=ApplicationBirthFrame.locals_store_other h.locals (fun v=>(h.separate v).symm) stored
  have fields:=SourceLocals.store_frame stored
  have well:=wellScoped_store h.well stored
  exact ⟨after,run,⟨rep,lm,h.separate,well⟩,fields.2.2.1⟩

theorem append_normal {F : Type} {context : Context F} {before middle after : State F}
    {xs ys : List Stmt} {flow : Flow} (first : ExecList context before xs .normal middle)
    (last : ExecList context middle ys flow after) : ExecList context before (xs++ys) flow after := by
  induction xs generalizing before with
  | nil=>cases first; exact last
  | cons x xs ih=>
    cases first with
    | cons run rest=>exact .cons run (ih rest)
    | abrupt run bad=>exact False.elim (bad rfl)

/-- Every literal store is an actual source assignment with a proved u64
conversion and pointer bound. This is not a certificate-supplied pi output. -/
theorem pi_stores_execution {F : Type} (context : Context F) (j : Nat) (hj : j≤5)
    {before : State F} {input : Input} {owner : Nat} {ids : Param → Nat}
    (h : ParamView before input owner ids (piData input.old input.layout.workStart 0)) :
    ∃after,ExecList context before (piStatements j) .normal after ∧
      ParamView after input owner ids (piData input.old input.layout.workStart j) ∧ after.scope=before.scope := by
  induction j with
  | zero=>exact ⟨before,.nil,h,rfl⟩
  | succ j ih=>
    obtain ⟨middle,run,view,scope⟩:=ih (by omega)
    obtain ⟨after,step,post,restored⟩:=pi_store_execution context view (by omega)
    have list : piStatements (j+1)=piStatements j++[piStatement j]:=by simp [piStatements,List.range_succ,List.map_append]
    refine ⟨after,?_,post,restored.trans scope⟩
    rw [list]; exact append_normal run (.cons step .nil)

/-- Complete six-statement source prefix: actual zeroing followed by all five
literal limb assignments, preserving arbitrary caller words outside work80. -/
theorem pi_prefix_execution {F : Type} (context : Context F)
    (selected : findFunction context.program "zero_words"=some zero_words_ast)
    {before : State F} {input : Input} {owner : Nat} {ids : Param → Nat}
    (h : ParamView before input owner ids input.old) (scope : before.scope=owner) :
    ∃after,ExecList context before prefixStatements .normal after ∧
      ParamView after input owner ids (piData input.old input.layout.workStart 5) ∧ after.scope=owner := by
  obtain ⟨middle,zero,view,middleScope⟩:=zero_execution context selected h scope
  obtain ⟨after,run,post,restored⟩:=pi_stores_execution context 5 (by omega) view
  exact ⟨after,.cons zero run,post,restored.trans middleScope⟩

#print axioms actual_prefix
#print axioms pi_prefix_execution
end RH080Next.FFTPV.RootSource
