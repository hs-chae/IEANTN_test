/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTFapSourceNumerics
import FFTMainIOOutput
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open Real MeasureTheory
namespace RH080Next.FFTPV.FapMain
open FFT FFT.IntegerModel MainCertificate MainSuffix MainFinish
open RH080Next.Explicit

/-- Independent source syntax plus a complete actual main execution, including
its nested norm call, cast, printf event and int-zero return. Generic allocation
and stdio success select a possible execution; failures are not excluded from
the universal source correctness theorem. -/
theorem actual_main_result : MainIO.Result .fap 781796015790084776 := by
  have actual:=MainIO.actual_result .fap fapCertificate
    (by rw [FapSource.norm_answer_checked];norm_num [AnswerSource.sentinel])
  simpa only [FapSource.norm_answer_checked] using actual

/-- The bound obtains its exact integer from the complete operational main
execution, not merely its static callsite or a separately supplied norm call. -/
theorem main_output_periodic_norm (out : Nat) (actual : MainIO.Result .fap out) :
    (∫ y in (0:ℝ)..1,|nodalPolynomial FapPV.Data.affineNodes y|)≤
      (out:ℝ)/1000000000000000000 := by
  have value:=(MainIO.result_value_eq fapCertificate actual).trans FapSource.norm_answer_checked
  rw [value]
  have h:=RH080Next.Primal.FapFFTKernel.kernel_periodic_norm
  rw [FapForest17.numerator_checked] at h
  exact h

/-- Full-main source-first numerical leaf. The BR norm identity remains an
explicit analytic input; compiler, ABI, generic stdio/flush, OS and hardware
contracts relate the model to independently recorded physical execution. -/
theorem source_first_actual_norm (hBRNorm : Explicit.SourceBRFourierNormFive) :
    (∫ u : ℝ,|inverseCosine (affineSpectrum FapPV.Data.affineNodes 80) u|)≤
      (7817960157900848:ℝ)/10000000000000000 := by
  rw [hBRNorm FapPV.Data.affineNodes 80 (by norm_num)
    (by simpa using FapPV.Data.affineNodes_length) RH080Next.Primal.FapFFTKernel.actual_terminal]
  exact (main_output_periodic_norm _ actual_main_result).trans (by norm_num)

#print axioms actual_main_result
#print axioms main_output_periodic_norm
#print axioms source_first_actual_norm
end RH080Next.FFTPV.FapMain
