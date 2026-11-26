/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTComplexMultiplyStep
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.ComplexSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings ApplicationBirthFrame

theorem caller_frame_trans {F : Type} {a b c : State F} {writes : List Nat}
    (first : MultiplyCall.CallerFrame a b writes) (second : MultiplyCall.CallerFrame b c writes) :
    MultiplyCall.CallerFrame a c writes:=by
  have narrowed : Frame a.nextObject b c writes:=by
    refine ⟨second.frame.well,first.frame.nextObject.trans second.frame.fresh,second.frame.nextObject,
      second.frame.nextScope,second.frame.mode,second.frame.foreign,?_⟩
    intro id old outside
    exact second.frame.outside id (old.trans_le first.frame.nextObject) outside
  exact ⟨second.environment.trans first.environment,second.scope.trans first.scope,first.frame.trans narrowed⟩

def productStatements : List Stmt:=
  [StatusCall.statement "fixed_multiply" (multiplyArguments 0),
    StatusCall.statement "fixed_multiply" (multiplyArguments 1),
    StatusCall.statement "fixed_multiply" (multiplyArguments 2),
    StatusCall.statement "fixed_multiply" (multiplyArguments 3)]

theorem consume_source_head {F : Type} {context : Context F} {before middle after : State F}
    {stmt : Stmt} {rest : List Stmt} {flow : Flow}
    (post : ∀other f,Exec context before stmt f other → f=.normal ∧ other=middle)
    (actual : ExecList context before (stmt::rest) flow after) : ExecList context middle rest flow after:=by
  cases actual with
  | cons head tail=>
    obtain ⟨_,same⟩:=post _ _ head
    cases same
    exact tail
  | abrupt head ne=>exact False.elim (ne (post _ _ head).1)

/-- All four actual source multiplication Calls, including real scope births,
status assignments and shared-workspace preservation, compute precisely the
four mathematical signed floors in the paired-integer FFT model. -/
theorem product_statements_execution {F : Type} (context : Context F)
    (selected : findFunction context.program "fixed_multiply"=some fixed_multiply_ast)
    (zeroSelected : findFunction context.program "zero_words"=some zero_words_ast)
    (incSelected : findFunction context.program "increment_words"=some increment_words_ast)
    (canonSelected : findFunction context.program "canonical_sign"=some FFTRecursivePV.canonical_sign_ast)
    {before : State F} {input : Input} {ids : PVar→Nat} {owner statusId : Nat} {workData : Nat→Nat}
    (h : View before input ids owner statusId 0 workData) :
    ∃after finalWork,ExecList context before productStatements .normal after ∧
      View after input ids owner statusId 4 finalWork ∧
      MultiplyCall.CallerFrame before after [input.layout.object .work] ∧
      ∀after' flow,ExecList context before productStatements flow after' →flow=.normal ∧ after'=after:=by
  obtain ⟨s1,d1,r0,h1,f0,u0⟩:=multiply_step context selected zeroSelected incSelected canonSelected (0:Fin 4) h
  obtain ⟨s2,d2,r1,h2,f1,u1⟩:=multiply_step context selected zeroSelected incSelected canonSelected (1:Fin 4) h1
  obtain ⟨s3,d3,r2,h3,f2,u2⟩:=multiply_step context selected zeroSelected incSelected canonSelected (2:Fin 4) h2
  obtain ⟨after,finalWork,r3,h4,f3,u3⟩:=multiply_step context selected zeroSelected incSelected canonSelected (3:Fin 4) h3
  refine ⟨after,finalWork,.cons r0 (.cons r1 (.cons r2 (.cons r3 .nil))),h4,
    caller_frame_trans (caller_frame_trans (caller_frame_trans f0 f1) f2) f3,?_⟩
  intro after' flow run
  have rest1:=consume_source_head u0 run
  have rest2:=consume_source_head u1 rest1
  have rest3:=consume_source_head u2 rest2
  have rest4:=consume_source_head u3 rest3
  cases rest4
  exact ⟨rfl,rfl⟩

#print axioms product_statements_execution
end RH080Next.FFTPV.ComplexSource
