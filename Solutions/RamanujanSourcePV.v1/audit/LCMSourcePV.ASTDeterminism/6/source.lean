/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import LCMSourcePV.ASTLoops

namespace LCMSourcePV.ASTLoops
open LCMSourcePV.Witness.C
universe u v
variable {State : Type u} {Value : Type v}
variable {Eval : Expr → State → State → Value → Prop}
variable {Declare : List Decl → State → State → Prop} {truth : Value → Bool}
variable {Scope : State → Flow State Value → Flow State Value → Prop}

def EvalDeterministic (E : Expr → State → State → Value → Prop) : Prop :=
  ∀ {e s t v t' v'}, E e s t v → E e s t' v' → t=t' ∧ v=v'
def DeclareDeterministic (D : List Decl → State → State → Prop) : Prop :=
  ∀ {ds s t t'}, D ds s t → D ds s t' → t=t'
def ScopeDeterministic (S : State → Flow State Value → Flow State Value → Prop) : Prop :=
  ∀ {s inner out out'}, S s inner out → S s inner out' → out=out'


 theorem guard_deterministic (hE : EvalDeterministic Eval) {cond s t flag t' flag'}
    (h : GuardRun Eval truth cond s t flag) (h' : GuardRun Eval truth cond s t' flag') :
    t=t' ∧ flag=flag' := by
  cases h with
  | omitted => cases h'; exact ⟨rfl,rfl⟩
  | present first =>
    cases h' with
    | present second =>
      obtain ⟨rfl,rfl⟩ := hE first second
      exact ⟨rfl,rfl⟩

#check @guard_deterministic
mutual
 theorem stmt_deterministic (hE : EvalDeterministic Eval) (hD : DeclareDeterministic Declare)
    (hS : ScopeDeterministic Scope) {body s out out'}
    (h : StmtRun Eval Declare truth Scope body s out)
    (h' : StmtRun Eval Declare truth Scope body s out') : out=out' := by
  cases h with
  | skip => cases h'; rfl
  | evaluate first =>
    cases h' with
    | evaluate second =>
      obtain ⟨rfl,_⟩ := hE first second
      rfl
  | declare first =>
    cases h' with
    | declare second =>
      obtain rfl := hD first second
      rfl
  | returnValue first =>
    cases h' with
    | returnValue second =>
      obtain ⟨rfl,rfl⟩ := hE first second
      rfl
  | branch test body =>
    cases h' with
    | branch test' body' =>
      obtain ⟨rfl,rfl⟩ := hE test test'
      exact stmt_deterministic (@hE) (@hD) (@hS) body body'
  | sequence run exit =>
    cases h' with
    | sequence run' exit' =>
      have same := seq_deterministic (@hE) (@hD) (@hS) run run'
      cases same
      exact hS exit exit'
  | forLoop init loop exit =>
    cases h' with
    | forLoop init' loop' exit' =>
      have sameInit := stmt_deterministic (@hE) (@hD) (@hS) init init'
      cases sameInit
      have same := for_deterministic (@hE) (@hD) (@hS) loop loop'
      cases same
      exact hS exit exit'
    | forInitialReturn init' exit' =>
      cases stmt_deterministic (@hE) (@hD) (@hS) init init'
  | forInitialReturn init exit =>
    cases h' with
    | forLoop init' loop' exit' =>
      cases stmt_deterministic (@hE) (@hD) (@hS) init init'
    | forInitialReturn init' exit' =>
      have same := stmt_deterministic (@hE) (@hD) (@hS) init init'
      cases same
      exact hS exit exit'
  | whileLoop loop =>
    cases h' with
    | whileLoop loop' => exact while_deterministic (@hE) (@hD) (@hS) loop loop'
 termination_by structural h

 theorem seq_deterministic (hE : EvalDeterministic Eval) (hD : DeclareDeterministic Declare)
    (hS : ScopeDeterministic Scope) {body s out out'}
    (h : SeqRun Eval Declare truth Scope body s out)
    (h' : SeqRun Eval Declare truth Scope body s out') : out=out' := by
  cases h with
  | nil => cases h'; rfl
  | next first rest =>
    cases h' with
    | next first' rest' =>
      have same := stmt_deterministic (@hE) (@hD) (@hS) first first'
      cases same
      exact seq_deterministic (@hE) (@hD) (@hS) rest rest'
    | returned first' => cases stmt_deterministic (@hE) (@hD) (@hS) first first'
  | returned first =>
    cases h' with
    | next first' rest' => cases stmt_deterministic (@hE) (@hD) (@hS) first first'
    | returned first' => exact stmt_deterministic (@hE) (@hD) (@hS) first first'
 termination_by structural h

 theorem for_deterministic (hE : EvalDeterministic Eval) (hD : DeclareDeterministic Declare)
    (hS : ScopeDeterministic Scope) {cond step body s out out'}
    (h : ForRun Eval Declare truth Scope cond step body s out)
    (h' : ForRun Eval Declare truth Scope cond step body s out') : out=out' := by
  cases h with
  | done test =>
    cases h' with
    | done test' =>
      obtain ⟨rfl,_⟩ := guard_deterministic (Eval := Eval) (truth := truth) hE test test'
      rfl
    | next test' iter inc rest =>
      have same := (guard_deterministic (Eval := Eval) (truth := truth) hE test test').2
      cases same
    | returned test' iter =>
      have same := (guard_deterministic (Eval := Eval) (truth := truth) hE test test').2
      cases same
  | next test iter inc rest =>
    cases h' with
    | done test' =>
      have same := (guard_deterministic (Eval := Eval) (truth := truth) hE test test').2
      cases same
    | next test' iter' inc' rest' =>
      obtain ⟨rfl,_⟩ := guard_deterministic (Eval := Eval) (truth := truth) hE test test'
      have sameIter := stmt_deterministic (@hE) (@hD) (@hS) iter iter'
      cases sameIter
      obtain ⟨rfl,_⟩ := hE inc inc'
      exact for_deterministic (@hE) (@hD) (@hS) rest rest'
    | returned test' iter' =>
      obtain ⟨rfl,_⟩ := guard_deterministic (Eval := Eval) (truth := truth) hE test test'
      cases stmt_deterministic (@hE) (@hD) (@hS) iter iter'
  | returned test iter =>
    cases h' with
    | done test' =>
      have same := (guard_deterministic (Eval := Eval) (truth := truth) hE test test').2
      cases same
    | next test' iter' inc' rest' =>
      obtain ⟨rfl,_⟩ := guard_deterministic (Eval := Eval) (truth := truth) hE test test'
      cases stmt_deterministic (@hE) (@hD) (@hS) iter iter'
    | returned test' iter' =>
      obtain ⟨rfl,_⟩ := guard_deterministic (Eval := Eval) (truth := truth) hE test test'
      exact stmt_deterministic (@hE) (@hD) (@hS) iter iter'
 termination_by structural h

 theorem while_deterministic (hE : EvalDeterministic Eval) (hD : DeclareDeterministic Declare)
    (hS : ScopeDeterministic Scope) {cond body s out out'}
    (h : WhileRun Eval Declare truth Scope cond body s out)
    (h' : WhileRun Eval Declare truth Scope cond body s out') : out=out' := by
  cases h with
  | done test stop =>
    cases h' with
    | done test' stop' =>
      obtain ⟨rfl,rfl⟩ := hE test test'
      rfl
    | next test' go iter rest =>
      obtain ⟨rfl,rfl⟩ := hE test test'
      simp_all
    | returned test' go iter =>
      obtain ⟨rfl,rfl⟩ := hE test test'
      simp_all
  | next test go iter rest =>
    cases h' with
    | done test' stop =>
      obtain ⟨rfl,rfl⟩ := hE test test'
      simp_all
    | next test' go' iter' rest' =>
      obtain ⟨rfl,rfl⟩ := hE test test'
      have same := stmt_deterministic (@hE) (@hD) (@hS) iter iter'
      cases same
      exact while_deterministic (@hE) (@hD) (@hS) rest rest'
    | returned test' go' iter' =>
      obtain ⟨rfl,rfl⟩ := hE test test'
      cases stmt_deterministic (@hE) (@hD) (@hS) iter iter'
  | returned test go iter =>
    cases h' with
    | done test' stop =>
      obtain ⟨rfl,rfl⟩ := hE test test'
      simp_all
    | next test' go' iter' rest' =>
      obtain ⟨rfl,rfl⟩ := hE test test'
      cases stmt_deterministic (@hE) (@hD) (@hS) iter iter'
    | returned test' go' iter' =>
      obtain ⟨rfl,rfl⟩ := hE test test'
      exact stmt_deterministic (@hE) (@hD) (@hS) iter iter'
 termination_by structural h
end

#print axioms stmt_deterministic
#print axioms seq_deterministic
#print axioms for_deterministic
#print axioms while_deterministic
end LCMSourcePV.ASTLoops
