/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTMainSuffixTable
import FFTBlockWhileScope
set_option autoImplicit false
namespace RH080Next.FFTPV.MainSuffix
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings

theorem pure_assignment_scope {F : Type} {context : Context F} {before after : State F}
    {target expression : Expr} {flow : Flow} (ct : SourcePure.CallFree target) (ce : SourcePure.CallFree expression)
    (actual : Exec context before (.assign target expression) flow after) : after.scope=before.scope := by
  cases actual with
  | assign ev pl st=>
    have a:=SourcePure.eval_state ev ce
    have b:=SourcePure.place_state pl ct
    subst_vars
    exact (SourceLocals.store_frame st).2.2.1

theorem pure_declaration_scope {F : Type} {context : Context F} {before after : State F}
    {type : CType} {name : String} {expression : Expr} {flow : Flow}
    (ce : SourcePure.CallFree expression)
    (actual : Exec context before (.declare type name (some expression)) flow after) : after.scope=before.scope := by
  cases actual with
  | declareSome ev dec=>
    have a:=SourcePure.eval_state ev ce
    subst_vars
    exact (SourceLocals.declare_frame dec).1

theorem table_scope {F : Type} {context : Context F} {before after : State F}
    (actual : ExecList context before
      [TwiddleSource.unitAssignment,TwiddleSource.jDeclaration,TwiddleSource.loop] .normal after) :
    after.scope=before.scope := by
  cases actual with
  | abrupt h no=>exact False.elim (no rfl)
  | cons h rest=>
    have a:=pure_assignment_scope (by trivial) (by trivial) h
    cases rest with
    | abrupt h no=>exact False.elim (no rfl)
    | cons h rest=>
      have b:=pure_declaration_scope (by trivial) h
      cases rest with
      | abrupt h no=>exact False.elim (no rfl)
      | cons h rest=>
        cases rest
        exact (BlockEnvironment.while_block_scope (by trivial) h).trans (b.trans a)

#print axioms pure_assignment_scope
#print axioms pure_declaration_scope
#print axioms table_scope
end RH080Next.FFTPV.MainSuffix
