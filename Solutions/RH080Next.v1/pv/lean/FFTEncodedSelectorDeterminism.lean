/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTEncodedSelectorBindings
import ExplicitFFTCompareDeterminism
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.EncodedSelector
open GoldbachDirect GoldbachDirect.Semantics

private theorem if_else_unique {F : Type} {context : Context F} {test : Expr} {yes no : Stmt}
    (pure : SourcePure.CallFree test) (yesUnique : CompareSource.Unique context yes)
    (noUnique : CompareSource.Unique context no) : CompareSource.Unique context (.ite test yes (some no)):=by
  intro before a b fa fb first second
  cases first with
  | ifTrue ev truth run=>
    cases second with
    | ifTrue ev' truth' run'=>
      obtain ⟨rfl,rfl⟩:=PureDeterminism.eval_unique pure ev ev'
      exact yesUnique run run'
    | ifElse ev' truth' run'=>
      cases (PureDeterminism.eval_unique pure ev ev').1
      simp_all
  | ifElse ev truth run=>
    cases second with
    | ifTrue ev' truth' run'=>
      cases (PureDeterminism.eval_unique pure ev ev').1
      simp_all
    | ifElse ev' truth' run'=>
      obtain ⟨rfl,rfl⟩:=PureDeterminism.eval_unique pure ev ev'
      exact noUnique run run'

theorem Tree.unique {F : Type} (context : Context F) (tree : Tree) : CompareSource.Unique context tree.statement:=by
  induction tree with
  | leaf v=>
    intro before a b fa fb first second
    exact PureDeterminism.simple_unique (by simp [Tree.statement,PureDeterminism.Simple,SourcePure.CallFree]) first second
  | branch cut left right ihl ihr=>
    apply if_else_unique (by simp [SourcePure.CallFree])
    · apply CompareSource.block_unique
      intro s member
      have same : s=left.statement:=by simpa using member
      subst s
      intro before a b fa fb first second
      exact ihl first second
    · apply CompareSource.block_unique
      intro s member
      have same : s=right.statement:=by simpa using member
      subst s
      intro before a b fa fb first second
      exact ihr first second

def body (length fallback : Nat) (tree : Tree) : List Stmt:=[guard length fallback,tree.statement]

theorem actual_body (length fallback : Nat) (tree : Tree) : (function length fallback tree).body=.block (body length fallback tree):=rfl

theorem guard_unique {F : Type} (context : Context F) (length fallback : Nat) : CompareSource.Unique context (guard length fallback):=by
  exact CompareSource.return_branch_unique _ _ (by trivial)

theorem body_unique {F : Type} {context : Context F} (length fallback : Nat) (tree : Tree)
    {before a b : State F} {fa fb : Flow}
    (first : Body context (body length fallback tree) before (body length fallback tree) fa a)
    (second : Body context (body length fallback tree) before (body length fallback tree) fb b) : fa=fb ∧ a=b:=by
  have unique : ∀s∈body length fallback tree,CompareSource.Unique context s:=by
    intro s member
    simp only [body,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl
    · exact guard_unique context length fallback
    · exact Tree.unique context tree
  cases first with
  | finish run _=>
    cases second with
    | finish run' _=>exact CompareSource.list_unique unique run run'
    | jump run' target rest=>cases tree <;> simp [body,guard,Tree.statement,labelTail] at target
  | jump run target rest=>cases tree <;> simp [body,guard,Tree.statement,labelTail] at target

#print axioms Tree.unique
#print axioms body_unique
end RH080Next.FFTPV.EncodedSelector
