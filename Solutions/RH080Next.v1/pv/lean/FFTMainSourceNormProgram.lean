/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTMainSourceNormCall
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
namespace RH080Next.FFTPV.MainSuffix
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals
open MainAllocation

/-- The independently proved correspondence of the complete actual C source
and AST is packaged with constructive whole-function execution and universal
correctness, including allocation failures. A literal numerical certificate
and the actual ANT consumer are supplied by the final application. -/
theorem source_norm_program_total {F : Type} (context : Context F) (p : InputLoader.Profile)
    (pinned : context.program=p.program) (certificate : MainCertificate.Certificate p)
    (has : HasMemory context) (sound : MemorySound context) :
    Correspondence.SourceSyntaxCorresponds p.source p.program ∧
    ∀(caller : State F),WellScoped caller → caller.mode=.host →
      (∃after,Call context (failureSourceFunction (isFap p)).name [.integer (integer64 p.grid)] caller
        (.value (.integer (integer64 (normAnswer p certificate)))) after) ∧
      (∀after result,Call context (failureSourceFunction (isFap p)).name [.integer (integer64 p.grid)] caller result after →
        result=.value allocationFailureValue ∨ result=.value (.integer (integer64 (normAnswer p certificate)))) := by
  refine ⟨p.actual_syntax,?_⟩
  intro caller well host
  exact ⟨norm_call_exists context p pinned certificate has sound caller well host,
    fun after result actual => every_norm_call context p pinned certificate has sound well host actual⟩

#print axioms source_norm_program_total
end RH080Next.FFTPV.MainSuffix
