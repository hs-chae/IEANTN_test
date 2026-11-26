/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTMainFreeReturn
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.MainAllocation
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings ApplicationBirthFrame RecursiveSource

def finalFreeOrder : List Role := [.data,.twiddle,.work,.output]

def normFinalStatements (fap : Bool) : List Stmt :=
  let function := if fap then FapFFTRecursivePV.fap_recursive_norm_upper_ast
    else FFTRecursivePV.w4_recursive_norm_upper_ast
  (bodyItems function).drop ((bodyItems function).length-5)

theorem actual_w4_final_statements : normFinalStatements false=finalStatements finalFreeOrder := by rfl
theorem actual_fap_final_statements : normFinalStatements true=finalStatements finalFreeOrder := by rfl

/-- The last five statements of each unchanged actual norm source release
the four application buffers in source order and return the real answer slot.
The result holds for every execution, including expression-order alternatives. -/
theorem FreeView.source_final_total {F : Type} (context : Context F) (fap : Bool)
    {before : State F} {n answerId answerOwner answer : Nat}
    {objects ids owners : Role → Nat} {data : Role → Nat → Nat}
    (h : FreeView before n objects ids owners data answerId answerOwner answer finalFreeOrder)
    (absent : findFunction context.program "free"=none) (has : HasMemory context)
    (sound : MemorySound context) :
    ∃after,ExecList context before (normFinalStatements fap)
        (.returned (.integer (integer64 answer))) after ∧
      (∀other flow,ExecList context before (normFinalStatements fap) flow other →
        flow=.returned (.integer (integer64 answer)) ∧ other=after) ∧
      after.environment=before.environment ∧ after.scope=before.scope ∧
      Frame before.nextObject before after (finalFreeOrder.map objects) := by
  have exactSource : normFinalStatements fap=finalStatements finalFreeOrder := by
    cases fap <;> rfl
  rw [exactSource]
  exact h.return_total context finalFreeOrder (by decide) absent has sound

#print axioms actual_w4_final_statements
#print axioms actual_fap_final_statements
#print axioms FreeView.source_final_total
end RH080Next.FFTPV.MainAllocation
