/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTMainSuffixMiddle
import FFTMainRecursiveStatement
import FFTMainFinishTotal
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
namespace RH080Next.FFTPV.MainSuffix
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings
open MainAllocation MainRootBirth RecursiveSource ApplicationBirthFrame

def normalizedTotal (p : InputLoader.Profile) (totalAbs : Nat) : Nat:=
  NormalizeSource.totalValue (isFap p) (FFT.Limbs.ceilQuotient totalAbs (1000000000^2)) p.grid

/-- The source algorithm's sentinel-aware answer, derived from the exact
independently kernel-verified FFT output and actual quadrature algorithm. -/
def normAnswer (p : InputLoader.Profile) (certificate : MainCertificate.Certificate p) : Nat:=
  MainFinish.finishValue (isFap p) p.grid (normalizedTotal p (FFT.IntegerModel.absSum certificate.output)) (QuadSource.scaledModel p)

def completeStatements (p : InputLoader.Profile) : List Stmt:=
  frontStatements p++[MainRecursiveStatement.statement]++middleStatements p++
    ((bodyItems (failureSourceFunction (isFap p))).drop 36)

theorem actual_successful_suffix (p : InputLoader.Profile) :
    normSuccessSuffix (failureSourceFunction (isFap p))=completeStatements p := by cases p <;> rfl

/-- Complete source execution from the actual successful NULL-test state.
Every typed buffer, local, initialized root, twiddle table, loaded vector,
FFT output, accumulator, upward rounding, guarded answer and release is
established from its actual source instructions. No successful application
execution, initialized representation or observed norm answer is assumed. -/
theorem norm_suffix_total {F : Type} (context : Context F) (p : InputLoader.Profile)
    (pinned : context.program=p.program) (certificate : MainCertificate.Certificate p)
    (has : HasMemory context) (sound : MemorySound context)
    {before : State F} {nId owner : Nat} {objects ids : Role → Nat}
    (raw : View before p.grid nId owner [.output,.work,.twiddle,.data] objects ids) :
    ∃after,MainFinish.ReturningSegment context before
      (normSuccessSuffix (failureSourceFunction (isFap p)))
      (.integer (integer64 (normAnswer p certificate))) after ∧ normAnswer p certificate<2^64 := by
  obtain ⟨loaded,pointerBase,status,jId,tableData,oldWork,frontRun,front⟩ := raw_to_loaded context p pinned raw
  obtain ⟨transformed,outputData,workData,recursiveRun,recursive⟩ := MainRecursiveStatement.execute context p pinned certificate front
  have arrays : ∀r,WordArrayRep transformed (objects r) (length p.grid r) (middleData p tableData outputData workData r) := by
    intro r;have h:=recursive.arrays r;cases r <;> exact h
  obtain ⟨summed,finalWork,middleRun,middle⟩ := sum_normalize_quad context p pinned recursive.full recursive.loader arrays
    recursive.scope recursive.well recursive.distinct recursive.outputDigits recursive.outputValues recursive.outputSmall
    recursive.totalZero recursive.quadZero
  have profilePinned : context.program=NormalizeSource.profileProgram (isFap p) := by cases p <;> exact pinned
  have positive : 0<p.grid := by cases p <;> decide
  have small : p.grid<1000000000 := by cases p <;> decide
  obtain ⟨after,finishRun,_,_,fits⟩ := MainFinish.source_finish_total context (isFap p) profilePinned middle.full middle.well
    middle.scope middle.distinct middle.arrays has sound positive small middle.totalDigits middle.quadDigits
  have receipt := recursive.partialSum_receipt (FFT.IntegerModel.absSum certificate.output) rfl
  have normalized : expectedTotal p (fun k => certificate.output.getD k (0,0))=
      normalizedTotal p (FFT.IntegerModel.absSum certificate.output) := by
    unfold expectedTotal normalizedTotal
    rw [receipt]
  have valueEq : MainFinish.finishValue (isFap p) p.grid
      (MainFinish.magnitudeAt (middleData p tableData outputData finalWork .work) 192)
      (MainFinish.magnitudeAt (middleData p tableData outputData finalWork .work) 208)=normAnswer p certificate := by
    change MainFinish.finishValue (isFap p) p.grid
      (FFT.Limbs.magnitude 1000000000 6 (fun k => finalWork (192+k)))
      (FFT.Limbs.magnitude 1000000000 6 (fun k => finalWork (208+k)))=normAnswer p certificate
    rw [middle.totalValue,middle.quadValue,normalized]
    rfl
  have last : MainFinish.ReturningSegment context summed
      ((bodyItems (failureSourceFunction (isFap p))).drop 36)
      (.integer (integer64 (normAnswer p certificate))) after := by
    simpa only [valueEq] using finishRun
  refine ⟨after,?_,?_⟩
  · rw [actual_successful_suffix]
    exact MainFinish.then_return ((frontRun.append recursiveRun).append middleRun) last
  · simpa only [valueEq] using fits

/-- Every source execution of the genuine nonNULL suffix returns precisely the
source-derived answer. This is the application lemma consumed by the complete
allocation-failure-or-correct-answer Call theorem. -/
theorem every_norm_suffix {F : Type} (context : Context F) (p : InputLoader.Profile)
    (pinned : context.program=p.program) (certificate : MainCertificate.Certificate p)
    (has : HasMemory context) (sound : MemorySound context)
    {before after : State F} {nId owner : Nat} {objects ids : Role → Nat} {flow : Flow}
    (raw : View before p.grid nId owner [.output,.work,.twiddle,.data] objects ids)
    (actual : ExecList context before (normSuccessSuffix (failureSourceFunction (isFap p))) flow after) :
    flow=.returned (.integer (integer64 (normAnswer p certificate))) := by
  obtain ⟨last,run,_⟩ := norm_suffix_total context p pinned certificate has sound raw
  exact (run.every after flow actual).1

#print axioms actual_successful_suffix
#print axioms norm_suffix_total
#print axioms every_norm_suffix
end RH080Next.FFTPV.MainSuffix
