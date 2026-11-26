/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTComplexAddStep
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.ComplexSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings ApplicationBirthFrame

def sumStatements : List Stmt:=
  [StatusCall.statement "fixed_add" (addArguments 0),StatusCall.statement "fixed_add" (addArguments 1)]

theorem sum_statements_execution {F : Type} (context : Context F)
    (selected : findFunction context.program "fixed_add"=some fixed_add_ast)
    (compareSelected : findFunction context.program "magnitude_compare"=some magnitude_compare_ast)
    (canonSelected : findFunction context.program "canonical_sign"=some FFTRecursivePV.canonical_sign_ast)
    {before : State F} {input : Input} {ids : PVar→Nat} {owner statusId : Nat} {workData outData : Nat→Nat}
    (h : SumView before input ids owner statusId 0 workData outData) :
    ∃after finalWork finalOut,ExecList context before sumStatements .normal after ∧
      SumView after input ids owner statusId 2 finalWork finalOut ∧
      MultiplyCall.CallerFrame before after [input.layout.object .output] ∧
      ∀after' flow,ExecList context before sumStatements flow after' →flow=.normal ∧ after'=after:=by
  obtain ⟨s1,w1,o1,r0,h1,f0,u0⟩:=add_step context selected compareSelected canonSelected (0:Fin 2) h
  obtain ⟨after,finalWork,finalOut,r1,h2,f1,u1⟩:=add_step context selected compareSelected canonSelected (1:Fin 2) h1
  refine ⟨after,finalWork,finalOut,.cons r0 (.cons r1 .nil),h2,caller_frame_trans f0 f1,?_⟩
  intro after' flow run
  have rest1:=consume_source_head u0 run
  have rest2:=consume_source_head u1 rest1
  cases rest2
  exact ⟨rfl,rfl⟩

#print axioms sum_statements_execution
end RH080Next.FFTPV.ComplexSource
