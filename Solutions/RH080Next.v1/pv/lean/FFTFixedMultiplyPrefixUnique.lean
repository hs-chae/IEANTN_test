/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTZeroCallDeterminism
import FFTFixedMultiplyInitializedCore
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.MultiplyCall
open GoldbachDirect GoldbachDirect.Semantics WordArrays

private theorem consume_head {F : Type} {context : Context F} {before middle after : State F}
    {stmt : Stmt} {rest : List Stmt} {flow : Flow}
    (post : ∀{other : State F} {f : Flow},Exec context before stmt f other → f=.normal ∧ other=middle)
    (actual : ExecList context before (stmt::rest) flow after) : ExecList context middle rest flow after:=by
  cases actual with
  | cons head tail=>
    obtain ⟨_,same⟩:=post head
    cases same
    exact tail
  | abrupt head ne=>exact False.elim (ne (post head).1)

/-- A known real prefix fixes every allowed competing execution through the
actual zero_words call, local declaration and complete nested core. -/
theorem consume_initialized_prefix {F : Type} {context : Context F}
    (zeroSelected : findFunction context.program "zero_words"=some zero_words_ast)
    {before current after : State F} {tail : List Stmt} {flow : Flow}
    (known : ExecList context before [MultiplyParameters.zeroCall,MultiplyParameters.iDeclaration,ProductOuter.outerLoop] .normal current)
    (actual : ExecList context before ([MultiplyParameters.zeroCall,MultiplyParameters.iDeclaration,ProductOuter.outerLoop]++tail) flow after) :
    ExecList context current tail flow after:=by
  cases known with
  | cons zeroRun rest=>
    have remaining:=consume_head (fun other=>ZeroCallUnique.expression_from_known zeroSelected zeroRun other) actual
    cases rest with
    | cons declaration rest=>
      have remaining':=consume_head (fun other=>by
        have unique:=PureDeterminism.simple_unique
          (by simp [MultiplyParameters.iDeclaration,PureDeterminism.Simple,SourcePure.CallFree]) declaration other
        exact ⟨unique.1.symm,unique.2.symm⟩) remaining
      cases rest with
      | cons core nil=>
        cases nil
        exact consume_head (fun other=>by
          have unique:=ProductOuter.outer_loop_unique context core other
          exact ⟨unique.1.symm,unique.2.symm⟩) remaining'
      | abrupt run ne=>exact False.elim (ne rfl)
    | abrupt run ne=>exact False.elim (ne rfl)
  | abrupt run ne=>exact False.elim (ne rfl)

#print axioms consume_initialized_prefix
end RH080Next.FFTPV.MultiplyCall
