/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTCompareBase
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.CompareSource
open GoldbachDirect GoldbachDirect.Semantics

/-- Determinism is proved from the actual operational rules; it is not an
additional source-execution premise. -/
def Unique {F : Type} (context : Context F) (stmt : Stmt) : Prop :=
  ∀{before a b : State F} {fa fb : Flow}, Exec context before stmt fa a →
    Exec context before stmt fb b → fa=fb ∧ a=b

theorem list_unique {F : Type} {context : Context F} {before a b : State F}
    {statements : List Stmt} {fa fb : Flow}
    (unique : ∀s∈statements,Unique context s)
    (first : ExecList context before statements fa a) (second : ExecList context before statements fb b) :
    fa=fb ∧ a=b := by
  induction statements generalizing before fa fb a b with
  | nil => cases first; cases second; exact ⟨rfl,rfl⟩
  | cons s ss ih =>
    have head : Unique context s := unique s (by simp)
    have tail : ∀s∈ss,Unique context s := fun s hs => unique s (by simp [hs])
    cases first with
    | cons one rest =>
      cases second with
      | cons one' rest' =>
        obtain ⟨_,rfl⟩ := head one one'
        exact ih tail rest rest'
      | abrupt one' abrupt => exact False.elim (abrupt (head one one').1.symm)
    | abrupt one abrupt =>
      cases second with
      | cons one' rest' => exact False.elim (abrupt (head one one').1)
      | abrupt one' abrupt' => exact head one one'

theorem block_unique {F : Type} {context : Context F} {statements : List Stmt}
    (unique : ∀s∈statements,Unique context s) : Unique context (.block statements) := by
  intro before a b fa fb first second
  cases first with | block entered run closed =>
    cases second with | block entered' run' closed' =>
      subst_vars
      obtain ⟨rfl,rfl⟩ := list_unique unique run run'
      exact ⟨rfl,rfl⟩

theorem return_branch_unique {F : Type} {context : Context F} (test : Expr) (n : Nat)
    (pure : SourcePure.CallFree test) : Unique context (.ite test (.block [returnStmt n]) none) := by
  intro before a b fa fb first second
  cases first with
  | ifTrue ev tr run =>
    cases second with
    | ifTrue ev' tr' run' =>
      obtain ⟨rfl,rfl⟩ := PureDeterminism.eval_unique pure ev ev'
      exact PureDeterminism.block_unique (by simp [PureDeterminism.Simple,returnStmt,SourcePure.CallFree]) run run'
    | ifFalse ev' tr' =>
      have eq := (PureDeterminism.eval_unique pure ev ev').1
      cases eq
      simp_all
  | ifFalse ev tr =>
    cases second with
    | ifTrue ev' tr' run' =>
      have eq := (PureDeterminism.eval_unique pure ev ev').1
      cases eq
      simp_all
    | ifFalse ev' tr' => exact ⟨rfl,(PureDeterminism.eval_unique pure ev ev').2⟩

theorem while_unique_aux {F : Type} {context : Context F}
    {before a : State F} {stmt : Stmt} {fa : Flow}
    (first : Exec context before stmt fa a) :
    ∀ (condition : Expr) (body : Stmt), stmt=.whileLoop condition body →
      SourcePure.CallFree condition → Unique context body →
      ∀{b : State F} {fb : Flow}, Exec context before (.whileLoop condition body) fb b → fa=fb ∧ a=b := by
  apply Exec.rec
    (motive_1 := fun _ _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ => True)
    (motive_5 := fun before stmt fa a _ =>
      ∀ (condition : Expr) (body : Stmt), stmt=.whileLoop condition body →
        SourcePure.CallFree condition → Unique context body →
        ∀{b : State F} {fb : Flow}, Exec context before (.whileLoop condition body) fb b → fa=fb ∧ a=b)
    (motive_6 := fun _ _ _ _ _ => True)
    (motive_7 := fun _ _ _ _ _ _ => True)
    (motive_8 := fun _ _ _ _ _ _ => True) (t:=first)
  all_goals try solve | intros; trivial | intros; contradiction
  case whileFalse =>
    intro before actualCondition value after actualBody ev tr _ condition body equality pure body_unique b fb second
    cases equality
    cases second with
    | whileFalse ev' tr' => exact ⟨rfl,(PureDeterminism.eval_unique pure ev ev').2⟩
    | whileNext ev' tr' run' rest' =>
      cases (PureDeterminism.eval_unique pure ev ev').1
      simp_all
    | whileContinue ev' tr' run' rest' =>
      cases (PureDeterminism.eval_unique pure ev ev').1
      simp_all
    | whileBreak ev' tr' run' =>
      cases (PureDeterminism.eval_unique pure ev ev').1
      simp_all
    | whileExit ev' tr' run' abrupt' =>
      cases (PureDeterminism.eval_unique pure ev ev').1
      simp_all
  case whileNext =>
    intro before actualCondition value tested actualBody middle flow after ev tr run rest _ bodyIH restIH condition body equality pure body_unique b fb second
    cases equality
    cases second with
    | whileFalse ev' tr' =>
      cases (PureDeterminism.eval_unique pure ev ev').1
      simp_all
    | whileNext ev' tr' run' rest' =>
      obtain ⟨rfl,rfl⟩ := PureDeterminism.eval_unique pure ev ev'
      obtain ⟨_,rfl⟩ := body_unique run run'
      exact restIH _ _ rfl pure body_unique rest'
    | whileContinue ev' tr' run' rest' =>
      obtain ⟨rfl,rfl⟩ := PureDeterminism.eval_unique pure ev ev'
      cases (body_unique run run').1
    | whileBreak ev' tr' run' =>
      obtain ⟨rfl,rfl⟩ := PureDeterminism.eval_unique pure ev ev'
      cases (body_unique run run').1
    | whileExit ev' tr' run' abrupt' =>
      obtain ⟨rfl,rfl⟩ := PureDeterminism.eval_unique pure ev ev'
      exact False.elim (abrupt'.1 (body_unique run run').1.symm)
  case whileContinue =>
    intro before actualCondition value tested actualBody middle flow after ev tr run rest _ bodyIH restIH condition body equality pure body_unique b fb second
    cases equality
    cases second with
    | whileFalse ev' tr' =>
      cases (PureDeterminism.eval_unique pure ev ev').1
      simp_all
    | whileNext ev' tr' run' rest' =>
      obtain ⟨rfl,rfl⟩ := PureDeterminism.eval_unique pure ev ev'
      cases (body_unique run run').1
    | whileContinue ev' tr' run' rest' =>
      obtain ⟨rfl,rfl⟩ := PureDeterminism.eval_unique pure ev ev'
      obtain ⟨_,rfl⟩ := body_unique run run'
      exact restIH _ _ rfl pure body_unique rest'
    | whileBreak ev' tr' run' =>
      obtain ⟨rfl,rfl⟩ := PureDeterminism.eval_unique pure ev ev'
      cases (body_unique run run').1
    | whileExit ev' tr' run' abrupt' =>
      obtain ⟨rfl,rfl⟩ := PureDeterminism.eval_unique pure ev ev'
      exact False.elim (abrupt'.2.2 (body_unique run run').1.symm)
  case whileBreak =>
    intro before actualCondition value tested actualBody after ev tr run _ bodyIH condition body equality pure body_unique b fb second
    cases equality
    cases second with
    | whileFalse ev' tr' =>
      cases (PureDeterminism.eval_unique pure ev ev').1
      simp_all
    | whileNext ev' tr' run' rest' =>
      obtain ⟨rfl,rfl⟩ := PureDeterminism.eval_unique pure ev ev'
      cases (body_unique run run').1
    | whileContinue ev' tr' run' rest' =>
      obtain ⟨rfl,rfl⟩ := PureDeterminism.eval_unique pure ev ev'
      cases (body_unique run run').1
    | whileBreak ev' tr' run' =>
      obtain ⟨rfl,rfl⟩ := PureDeterminism.eval_unique pure ev ev'
      exact ⟨rfl,(body_unique run run').2⟩
    | whileExit ev' tr' run' abrupt' =>
      obtain ⟨rfl,rfl⟩ := PureDeterminism.eval_unique pure ev ev'
      exact False.elim (abrupt'.2.1 (body_unique run run').1.symm)
  case whileExit =>
    intro before actualCondition value tested actualBody flow after ev tr run abrupt _ bodyIH condition body equality pure body_unique b fb second
    cases equality
    cases second with
    | whileFalse ev' tr' =>
      cases (PureDeterminism.eval_unique pure ev ev').1
      simp_all
    | whileNext ev' tr' run' rest' =>
      obtain ⟨rfl,rfl⟩ := PureDeterminism.eval_unique pure ev ev'
      exact False.elim (abrupt.1 (body_unique run run').1)
    | whileContinue ev' tr' run' rest' =>
      obtain ⟨rfl,rfl⟩ := PureDeterminism.eval_unique pure ev ev'
      exact False.elim (abrupt.2.2 (body_unique run run').1)
    | whileBreak ev' tr' run' =>
      obtain ⟨rfl,rfl⟩ := PureDeterminism.eval_unique pure ev ev'
      exact False.elim (abrupt.2.1 (body_unique run run').1)
    | whileExit ev' tr' run' abrupt' =>
      obtain ⟨rfl,rfl⟩ := PureDeterminism.eval_unique pure ev ev'
      exact body_unique run run'

theorem while_unique {F : Type} {context : Context F} {condition : Expr} {body : Stmt}
    (pure : SourcePure.CallFree condition) (body_unique : Unique context body)
    {before a b : State F} {fa fb : Flow}
    (first : Exec context before (.whileLoop condition body) fa a)
    (second : Exec context before (.whileLoop condition body) fb b) : fa=fb ∧ a=b :=
  while_unique_aux first condition body rfl pure body_unique second

theorem actual_body_unique {F : Type} (context : Context F) : Unique context loopBody := by
  apply block_unique
  intro stmt h
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at h
  rcases h with rfl | rfl | rfl
  · exact fun first second => PureDeterminism.simple_unique
      (by simp [decrement,PureDeterminism.Simple,SourcePure.CallFree]) first second
  · exact return_branch_unique _ _ (by simp [comparison,index,SourcePure.CallFree])
  · exact return_branch_unique _ _ (by simp [comparison,index,SourcePure.CallFree])

theorem actual_loop_unique {F : Type} (context : Context F) : Unique context loop :=
  while_unique (by simp [condition,SourcePure.CallFree]) (actual_body_unique context)

#print axioms while_unique
#print axioms actual_body_unique
#print axioms actual_loop_unique
end RH080Next.FFTPV.CompareSource
