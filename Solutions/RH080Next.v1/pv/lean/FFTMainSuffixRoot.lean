/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTMainRootBirthTotal
import FFTMainFailureView
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.MainSuffix
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots
open MainAllocation MainRootBirth RecursiveSource ApplicationBirthFrame

/-- The actual source instructions after the four successful NULL tests through
root initialization. The input consists of raw calloc byte arrays. -/
def rootPrefix : List Stmt:=zeroPrefix++rootBirthStatements

theorem actual_w4_root_prefix : ((bodyItems FFTRecursivePV.w4_recursive_norm_upper_ast).drop 8).take 9=rootPrefix := by rfl
theorem actual_fap_root_prefix : ((bodyItems FapFFTRecursivePV.fap_recursive_norm_upper_ast).drop 8).take 9=rootPrefix := by rfl

/-- No initialized application array or successful root value is assumed:
the four actual zeroing calls and all five actual root-birth instructions
establish the complete root-ready state. All allowed executions agree. -/
theorem raw_to_root {F : Type} (context : Context F)
    (pinned : context.program=FFTRecursivePV.program ∨ context.program=FapFFTRecursivePV.program)
    {before : State F} {n nId owner : Nat} {objects ids : Role→Nat}
    (raw : View before n nId owner [.output,.work,.twiddle,.data] objects ids)
    (grid : RootSource.OriginalGrid n) :
    ∃after pointerBase status workData,
      NormalSegment context before rootPrefix after ∧
      Ready after n nId owner objects ids pointerBase status workData := by
  have selected : findFunction context.program "zero_words"=some zero_words_ast := by
    rcases pinned with h|h <;> rw [h] <;> rfl
  have small : n≤2^24 := by rcases grid with rfl|rfl <;> decide
  obtain ⟨zeroAfter,zeroRun,initialized,_⟩:=raw.initialized.all_zero_steps context small selected
  have functions : RootSource.Functions context := by
    constructor <;> (rcases pinned with h|h <;> rw [h] <;> rfl)
  have rootSelected : findFunction context.program "initialize_root"=some initialize_root_ast := by
    rcases pinned with h|h <;> rw [h] <;> rfl
  obtain ⟨after,status,workData,rootRun,ready,_⟩:=from_initialized context functions rootSelected initialized grid
  exact ⟨after,zeroAfter.nextObject,status,workData,zeroRun.append rootRun,ready⟩

#print axioms actual_w4_root_prefix
#print axioms actual_fap_root_prefix
#print axioms raw_to_root
end RH080Next.FFTPV.MainSuffix
