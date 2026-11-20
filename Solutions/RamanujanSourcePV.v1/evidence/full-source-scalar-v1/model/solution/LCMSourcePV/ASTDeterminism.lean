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


theorem stmt_deterministic (hE : EvalDeterministic Eval) (hD : DeclareDeterministic Declare)
    (hS : ScopeDeterministic Scope) {body s out out'}
    (h : StmtRun Eval Declare truth Scope body s out)
    (h' : StmtRun Eval Declare truth Scope body s out') : out=out' := by
  revert out'
  refine StmtRun.rec 
    (motive_1 := fun body s out _ => ∀{other}, StmtRun Eval Declare truth Scope body s other → out=other)
    (motive_2 := fun body s out _ => ∀{other}, SeqRun Eval Declare truth Scope body s other → out=other)
    (motive_3 := fun cond step body s out _ => ∀{other}, ForRun Eval Declare truth Scope cond step body s other → out=other)
    (motive_4 := fun cond body s out _ => ∀{other}, WhileRun Eval Declare truth Scope cond body s other → out=other)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  · intro s out' other
    cases other
    rfl
  · intro e s t value first out' other
    cases other with
    | evaluate second =>
      obtain ⟨rfl,_⟩ := hE first second
      rfl
  · intro decls s t first out' other
    cases other with
    | declare second =>
      obtain rfl := hD first second
      rfl
  · intro e s t value first out' other
    cases other with
    | returnValue second =>
      obtain ⟨rfl,rfl⟩ := hE first second
      rfl
  · intro e yes no s t value result test body ih out' other
    cases other with
    | branch test' body' =>
      obtain ⟨rfl,rfl⟩ := hE test test'
      exact ih body'
  · intro body s inner result run exit ih out' other
    cases other with
    | sequence run' exit' =>
      have same := ih run'
      cases same
      exact hS exit exit'
  · intro init cond step body s t inner result initial loop exit ihInit ihLoop out' other
    cases other with
    | forLoop initial' loop' exit' =>
      have sameInit := ihInit initial'
      cases sameInit
      have same := ihLoop loop'
      cases same
      exact hS exit exit'
    | forInitialReturn initial' exit' =>
      cases ihInit initial'
  · intro init cond step body s t value result initial exit ihInit out' other
    cases other with
    | forLoop initial' loop' exit' => cases ihInit initial'
    | forInitialReturn initial' exit' =>
      have same := ihInit initial'
      cases same
      exact hS exit exit'
  · intro cond body s result loop ih out' other
    cases other with
    | whileLoop loop' => exact ih loop'
  · intro s out' other
    cases other
    rfl
  · intro head tail s t result first rest ihFirst ihRest out' other
    cases other with
    | next first' rest' =>
      have same := ihFirst first'
      cases same
      exact ihRest rest'
    | returned first' => cases ihFirst first'
  · intro head tail s t value first ihFirst out' other
    cases other with
    | next first' rest' => cases ihFirst first'
    | returned first' => exact ihFirst first'
  · intro cond step body s t test out' other
    cases other with
    | done test' =>
      obtain ⟨rfl,_⟩ := guard_deterministic (Eval:=Eval) (truth:=truth) hE test test'
      rfl
    | next test' iter inc rest =>
      have same := (guard_deterministic (Eval:=Eval) (truth:=truth) hE test test').2
      cases same
    | returned test' iter =>
      have same := (guard_deterministic (Eval:=Eval) (truth:=truth) hE test test').2
      cases same
  · intro cond step body s t b c value result test iter inc rest ihIter ihRest out' other
    cases other with
    | done test' =>
      have same := (guard_deterministic (Eval:=Eval) (truth:=truth) hE test test').2
      cases same
    | next test' iter' inc' rest' =>
      obtain ⟨rfl,_⟩ := guard_deterministic (Eval:=Eval) (truth:=truth) hE test test'
      have sameIter := ihIter iter'
      cases sameIter
      obtain ⟨rfl,_⟩ := hE inc inc'
      exact ihRest rest'
    | returned test' iter' =>
      obtain ⟨rfl,_⟩ := guard_deterministic (Eval:=Eval) (truth:=truth) hE test test'
      cases ihIter iter'
  · intro cond step body s t b value test iter ihIter out' other
    cases other with
    | done test' =>
      have same := (guard_deterministic (Eval:=Eval) (truth:=truth) hE test test').2
      cases same
    | next test' iter' inc' rest' =>
      obtain ⟨rfl,_⟩ := guard_deterministic (Eval:=Eval) (truth:=truth) hE test test'
      cases ihIter iter'
    | returned test' iter' =>
      obtain ⟨rfl,_⟩ := guard_deterministic (Eval:=Eval) (truth:=truth) hE test test'
      exact ihIter iter'
  · intro cond body s t value test stop out' other
    cases other with
    | done test' stop' =>
      obtain ⟨rfl,rfl⟩ := hE test test'
      rfl
    | next test' go iter rest =>
      obtain ⟨rfl,rfl⟩ := hE test test'
      simp_all
    | returned test' go iter =>
      obtain ⟨rfl,rfl⟩ := hE test test'
      simp_all
  · intro cond body s t b value result test go iter rest ihIter ihRest out' other
    cases other with
    | done test' stop =>
      obtain ⟨rfl,rfl⟩ := hE test test'
      simp_all
    | next test' go' iter' rest' =>
      obtain ⟨rfl,rfl⟩ := hE test test'
      have same := ihIter iter'
      cases same
      exact ihRest rest'
    | returned test' go' iter' =>
      obtain ⟨rfl,rfl⟩ := hE test test'
      cases ihIter iter'
  · intro cond body s t b condition value test go iter ihIter out' other
    cases other with
    | done test' stop =>
      obtain ⟨rfl,rfl⟩ := hE test test'
      simp_all
    | next test' go' iter' rest' =>
      obtain ⟨rfl,rfl⟩ := hE test test'
      cases ihIter iter'
    | returned test' go' iter' =>
      obtain ⟨rfl,rfl⟩ := hE test test'
      exact ihIter iter'

theorem seq_deterministic (hE : EvalDeterministic Eval) (hD : DeclareDeterministic Declare)
    (hS : ScopeDeterministic Scope) {body s out out'}
    (h : SeqRun Eval Declare truth Scope body s out)
    (h' : SeqRun Eval Declare truth Scope body s out') : out=out' := by
  revert out'
  refine SeqRun.rec 
    (motive_1 := fun body s out _ => ∀{other}, StmtRun Eval Declare truth Scope body s other → out=other)
    (motive_2 := fun body s out _ => ∀{other}, SeqRun Eval Declare truth Scope body s other → out=other)
    (motive_3 := fun cond step body s out _ => ∀{other}, ForRun Eval Declare truth Scope cond step body s other → out=other)
    (motive_4 := fun cond body s out _ => ∀{other}, WhileRun Eval Declare truth Scope cond body s other → out=other)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  · intro s out' other
    cases other
    rfl
  · intro e s t value first out' other
    cases other with
    | evaluate second =>
      obtain ⟨rfl,_⟩ := hE first second
      rfl
  · intro decls s t first out' other
    cases other with
    | declare second =>
      obtain rfl := hD first second
      rfl
  · intro e s t value first out' other
    cases other with
    | returnValue second =>
      obtain ⟨rfl,rfl⟩ := hE first second
      rfl
  · intro e yes no s t value result test body ih out' other
    cases other with
    | branch test' body' =>
      obtain ⟨rfl,rfl⟩ := hE test test'
      exact ih body'
  · intro body s inner result run exit ih out' other
    cases other with
    | sequence run' exit' =>
      have same := ih run'
      cases same
      exact hS exit exit'
  · intro init cond step body s t inner result initial loop exit ihInit ihLoop out' other
    cases other with
    | forLoop initial' loop' exit' =>
      have sameInit := ihInit initial'
      cases sameInit
      have same := ihLoop loop'
      cases same
      exact hS exit exit'
    | forInitialReturn initial' exit' =>
      cases ihInit initial'
  · intro init cond step body s t value result initial exit ihInit out' other
    cases other with
    | forLoop initial' loop' exit' => cases ihInit initial'
    | forInitialReturn initial' exit' =>
      have same := ihInit initial'
      cases same
      exact hS exit exit'
  · intro cond body s result loop ih out' other
    cases other with
    | whileLoop loop' => exact ih loop'
  · intro s out' other
    cases other
    rfl
  · intro head tail s t result first rest ihFirst ihRest out' other
    cases other with
    | next first' rest' =>
      have same := ihFirst first'
      cases same
      exact ihRest rest'
    | returned first' => cases ihFirst first'
  · intro head tail s t value first ihFirst out' other
    cases other with
    | next first' rest' => cases ihFirst first'
    | returned first' => exact ihFirst first'
  · intro cond step body s t test out' other
    cases other with
    | done test' =>
      obtain ⟨rfl,_⟩ := guard_deterministic (Eval:=Eval) (truth:=truth) hE test test'
      rfl
    | next test' iter inc rest =>
      have same := (guard_deterministic (Eval:=Eval) (truth:=truth) hE test test').2
      cases same
    | returned test' iter =>
      have same := (guard_deterministic (Eval:=Eval) (truth:=truth) hE test test').2
      cases same
  · intro cond step body s t b c value result test iter inc rest ihIter ihRest out' other
    cases other with
    | done test' =>
      have same := (guard_deterministic (Eval:=Eval) (truth:=truth) hE test test').2
      cases same
    | next test' iter' inc' rest' =>
      obtain ⟨rfl,_⟩ := guard_deterministic (Eval:=Eval) (truth:=truth) hE test test'
      have sameIter := ihIter iter'
      cases sameIter
      obtain ⟨rfl,_⟩ := hE inc inc'
      exact ihRest rest'
    | returned test' iter' =>
      obtain ⟨rfl,_⟩ := guard_deterministic (Eval:=Eval) (truth:=truth) hE test test'
      cases ihIter iter'
  · intro cond step body s t b value test iter ihIter out' other
    cases other with
    | done test' =>
      have same := (guard_deterministic (Eval:=Eval) (truth:=truth) hE test test').2
      cases same
    | next test' iter' inc' rest' =>
      obtain ⟨rfl,_⟩ := guard_deterministic (Eval:=Eval) (truth:=truth) hE test test'
      cases ihIter iter'
    | returned test' iter' =>
      obtain ⟨rfl,_⟩ := guard_deterministic (Eval:=Eval) (truth:=truth) hE test test'
      exact ihIter iter'
  · intro cond body s t value test stop out' other
    cases other with
    | done test' stop' =>
      obtain ⟨rfl,rfl⟩ := hE test test'
      rfl
    | next test' go iter rest =>
      obtain ⟨rfl,rfl⟩ := hE test test'
      simp_all
    | returned test' go iter =>
      obtain ⟨rfl,rfl⟩ := hE test test'
      simp_all
  · intro cond body s t b value result test go iter rest ihIter ihRest out' other
    cases other with
    | done test' stop =>
      obtain ⟨rfl,rfl⟩ := hE test test'
      simp_all
    | next test' go' iter' rest' =>
      obtain ⟨rfl,rfl⟩ := hE test test'
      have same := ihIter iter'
      cases same
      exact ihRest rest'
    | returned test' go' iter' =>
      obtain ⟨rfl,rfl⟩ := hE test test'
      cases ihIter iter'
  · intro cond body s t b condition value test go iter ihIter out' other
    cases other with
    | done test' stop =>
      obtain ⟨rfl,rfl⟩ := hE test test'
      simp_all
    | next test' go' iter' rest' =>
      obtain ⟨rfl,rfl⟩ := hE test test'
      cases ihIter iter'
    | returned test' go' iter' =>
      obtain ⟨rfl,rfl⟩ := hE test test'
      exact ihIter iter'

theorem for_deterministic (hE : EvalDeterministic Eval) (hD : DeclareDeterministic Declare)
    (hS : ScopeDeterministic Scope) {cond step body s out out'}
    (h : ForRun Eval Declare truth Scope cond step body s out)
    (h' : ForRun Eval Declare truth Scope cond step body s out') : out=out' := by
  revert out'
  refine ForRun.rec 
    (motive_1 := fun body s out _ => ∀{other}, StmtRun Eval Declare truth Scope body s other → out=other)
    (motive_2 := fun body s out _ => ∀{other}, SeqRun Eval Declare truth Scope body s other → out=other)
    (motive_3 := fun cond step body s out _ => ∀{other}, ForRun Eval Declare truth Scope cond step body s other → out=other)
    (motive_4 := fun cond body s out _ => ∀{other}, WhileRun Eval Declare truth Scope cond body s other → out=other)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  · intro s out' other
    cases other
    rfl
  · intro e s t value first out' other
    cases other with
    | evaluate second =>
      obtain ⟨rfl,_⟩ := hE first second
      rfl
  · intro decls s t first out' other
    cases other with
    | declare second =>
      obtain rfl := hD first second
      rfl
  · intro e s t value first out' other
    cases other with
    | returnValue second =>
      obtain ⟨rfl,rfl⟩ := hE first second
      rfl
  · intro e yes no s t value result test body ih out' other
    cases other with
    | branch test' body' =>
      obtain ⟨rfl,rfl⟩ := hE test test'
      exact ih body'
  · intro body s inner result run exit ih out' other
    cases other with
    | sequence run' exit' =>
      have same := ih run'
      cases same
      exact hS exit exit'
  · intro init cond step body s t inner result initial loop exit ihInit ihLoop out' other
    cases other with
    | forLoop initial' loop' exit' =>
      have sameInit := ihInit initial'
      cases sameInit
      have same := ihLoop loop'
      cases same
      exact hS exit exit'
    | forInitialReturn initial' exit' =>
      cases ihInit initial'
  · intro init cond step body s t value result initial exit ihInit out' other
    cases other with
    | forLoop initial' loop' exit' => cases ihInit initial'
    | forInitialReturn initial' exit' =>
      have same := ihInit initial'
      cases same
      exact hS exit exit'
  · intro cond body s result loop ih out' other
    cases other with
    | whileLoop loop' => exact ih loop'
  · intro s out' other
    cases other
    rfl
  · intro head tail s t result first rest ihFirst ihRest out' other
    cases other with
    | next first' rest' =>
      have same := ihFirst first'
      cases same
      exact ihRest rest'
    | returned first' => cases ihFirst first'
  · intro head tail s t value first ihFirst out' other
    cases other with
    | next first' rest' => cases ihFirst first'
    | returned first' => exact ihFirst first'
  · intro cond step body s t test out' other
    cases other with
    | done test' =>
      obtain ⟨rfl,_⟩ := guard_deterministic (Eval:=Eval) (truth:=truth) hE test test'
      rfl
    | next test' iter inc rest =>
      have same := (guard_deterministic (Eval:=Eval) (truth:=truth) hE test test').2
      cases same
    | returned test' iter =>
      have same := (guard_deterministic (Eval:=Eval) (truth:=truth) hE test test').2
      cases same
  · intro cond step body s t b c value result test iter inc rest ihIter ihRest out' other
    cases other with
    | done test' =>
      have same := (guard_deterministic (Eval:=Eval) (truth:=truth) hE test test').2
      cases same
    | next test' iter' inc' rest' =>
      obtain ⟨rfl,_⟩ := guard_deterministic (Eval:=Eval) (truth:=truth) hE test test'
      have sameIter := ihIter iter'
      cases sameIter
      obtain ⟨rfl,_⟩ := hE inc inc'
      exact ihRest rest'
    | returned test' iter' =>
      obtain ⟨rfl,_⟩ := guard_deterministic (Eval:=Eval) (truth:=truth) hE test test'
      cases ihIter iter'
  · intro cond step body s t b value test iter ihIter out' other
    cases other with
    | done test' =>
      have same := (guard_deterministic (Eval:=Eval) (truth:=truth) hE test test').2
      cases same
    | next test' iter' inc' rest' =>
      obtain ⟨rfl,_⟩ := guard_deterministic (Eval:=Eval) (truth:=truth) hE test test'
      cases ihIter iter'
    | returned test' iter' =>
      obtain ⟨rfl,_⟩ := guard_deterministic (Eval:=Eval) (truth:=truth) hE test test'
      exact ihIter iter'
  · intro cond body s t value test stop out' other
    cases other with
    | done test' stop' =>
      obtain ⟨rfl,rfl⟩ := hE test test'
      rfl
    | next test' go iter rest =>
      obtain ⟨rfl,rfl⟩ := hE test test'
      simp_all
    | returned test' go iter =>
      obtain ⟨rfl,rfl⟩ := hE test test'
      simp_all
  · intro cond body s t b value result test go iter rest ihIter ihRest out' other
    cases other with
    | done test' stop =>
      obtain ⟨rfl,rfl⟩ := hE test test'
      simp_all
    | next test' go' iter' rest' =>
      obtain ⟨rfl,rfl⟩ := hE test test'
      have same := ihIter iter'
      cases same
      exact ihRest rest'
    | returned test' go' iter' =>
      obtain ⟨rfl,rfl⟩ := hE test test'
      cases ihIter iter'
  · intro cond body s t b condition value test go iter ihIter out' other
    cases other with
    | done test' stop =>
      obtain ⟨rfl,rfl⟩ := hE test test'
      simp_all
    | next test' go' iter' rest' =>
      obtain ⟨rfl,rfl⟩ := hE test test'
      cases ihIter iter'
    | returned test' go' iter' =>
      obtain ⟨rfl,rfl⟩ := hE test test'
      exact ihIter iter'

theorem while_deterministic (hE : EvalDeterministic Eval) (hD : DeclareDeterministic Declare)
    (hS : ScopeDeterministic Scope) {cond body s out out'}
    (h : WhileRun Eval Declare truth Scope cond body s out)
    (h' : WhileRun Eval Declare truth Scope cond body s out') : out=out' := by
  revert out'
  refine WhileRun.rec 
    (motive_1 := fun body s out _ => ∀{other}, StmtRun Eval Declare truth Scope body s other → out=other)
    (motive_2 := fun body s out _ => ∀{other}, SeqRun Eval Declare truth Scope body s other → out=other)
    (motive_3 := fun cond step body s out _ => ∀{other}, ForRun Eval Declare truth Scope cond step body s other → out=other)
    (motive_4 := fun cond body s out _ => ∀{other}, WhileRun Eval Declare truth Scope cond body s other → out=other)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  · intro s out' other
    cases other
    rfl
  · intro e s t value first out' other
    cases other with
    | evaluate second =>
      obtain ⟨rfl,_⟩ := hE first second
      rfl
  · intro decls s t first out' other
    cases other with
    | declare second =>
      obtain rfl := hD first second
      rfl
  · intro e s t value first out' other
    cases other with
    | returnValue second =>
      obtain ⟨rfl,rfl⟩ := hE first second
      rfl
  · intro e yes no s t value result test body ih out' other
    cases other with
    | branch test' body' =>
      obtain ⟨rfl,rfl⟩ := hE test test'
      exact ih body'
  · intro body s inner result run exit ih out' other
    cases other with
    | sequence run' exit' =>
      have same := ih run'
      cases same
      exact hS exit exit'
  · intro init cond step body s t inner result initial loop exit ihInit ihLoop out' other
    cases other with
    | forLoop initial' loop' exit' =>
      have sameInit := ihInit initial'
      cases sameInit
      have same := ihLoop loop'
      cases same
      exact hS exit exit'
    | forInitialReturn initial' exit' =>
      cases ihInit initial'
  · intro init cond step body s t value result initial exit ihInit out' other
    cases other with
    | forLoop initial' loop' exit' => cases ihInit initial'
    | forInitialReturn initial' exit' =>
      have same := ihInit initial'
      cases same
      exact hS exit exit'
  · intro cond body s result loop ih out' other
    cases other with
    | whileLoop loop' => exact ih loop'
  · intro s out' other
    cases other
    rfl
  · intro head tail s t result first rest ihFirst ihRest out' other
    cases other with
    | next first' rest' =>
      have same := ihFirst first'
      cases same
      exact ihRest rest'
    | returned first' => cases ihFirst first'
  · intro head tail s t value first ihFirst out' other
    cases other with
    | next first' rest' => cases ihFirst first'
    | returned first' => exact ihFirst first'
  · intro cond step body s t test out' other
    cases other with
    | done test' =>
      obtain ⟨rfl,_⟩ := guard_deterministic (Eval:=Eval) (truth:=truth) hE test test'
      rfl
    | next test' iter inc rest =>
      have same := (guard_deterministic (Eval:=Eval) (truth:=truth) hE test test').2
      cases same
    | returned test' iter =>
      have same := (guard_deterministic (Eval:=Eval) (truth:=truth) hE test test').2
      cases same
  · intro cond step body s t b c value result test iter inc rest ihIter ihRest out' other
    cases other with
    | done test' =>
      have same := (guard_deterministic (Eval:=Eval) (truth:=truth) hE test test').2
      cases same
    | next test' iter' inc' rest' =>
      obtain ⟨rfl,_⟩ := guard_deterministic (Eval:=Eval) (truth:=truth) hE test test'
      have sameIter := ihIter iter'
      cases sameIter
      obtain ⟨rfl,_⟩ := hE inc inc'
      exact ihRest rest'
    | returned test' iter' =>
      obtain ⟨rfl,_⟩ := guard_deterministic (Eval:=Eval) (truth:=truth) hE test test'
      cases ihIter iter'
  · intro cond step body s t b value test iter ihIter out' other
    cases other with
    | done test' =>
      have same := (guard_deterministic (Eval:=Eval) (truth:=truth) hE test test').2
      cases same
    | next test' iter' inc' rest' =>
      obtain ⟨rfl,_⟩ := guard_deterministic (Eval:=Eval) (truth:=truth) hE test test'
      cases ihIter iter'
    | returned test' iter' =>
      obtain ⟨rfl,_⟩ := guard_deterministic (Eval:=Eval) (truth:=truth) hE test test'
      exact ihIter iter'
  · intro cond body s t value test stop out' other
    cases other with
    | done test' stop' =>
      obtain ⟨rfl,rfl⟩ := hE test test'
      rfl
    | next test' go iter rest =>
      obtain ⟨rfl,rfl⟩ := hE test test'
      simp_all
    | returned test' go iter =>
      obtain ⟨rfl,rfl⟩ := hE test test'
      simp_all
  · intro cond body s t b value result test go iter rest ihIter ihRest out' other
    cases other with
    | done test' stop =>
      obtain ⟨rfl,rfl⟩ := hE test test'
      simp_all
    | next test' go' iter' rest' =>
      obtain ⟨rfl,rfl⟩ := hE test test'
      have same := ihIter iter'
      cases same
      exact ihRest rest'
    | returned test' go' iter' =>
      obtain ⟨rfl,rfl⟩ := hE test test'
      cases ihIter iter'
  · intro cond body s t b condition value test go iter ihIter out' other
    cases other with
    | done test' stop =>
      obtain ⟨rfl,rfl⟩ := hE test test'
      simp_all
    | next test' go' iter' rest' =>
      obtain ⟨rfl,rfl⟩ := hE test test'
      cases ihIter iter'
    | returned test' go' iter' =>
      obtain ⟨rfl,rfl⟩ := hE test test'
      exact ihIter iter'

#print axioms stmt_deterministic
#print axioms seq_deterministic
#print axioms for_deterministic
#print axioms while_deterministic
end LCMSourcePV.ASTLoops
