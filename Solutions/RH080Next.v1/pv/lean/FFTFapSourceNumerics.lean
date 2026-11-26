/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTFapSourceCertificate
import FFTSourceOutput
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2000000
noncomputable section
open Real MeasureTheory
namespace RH080Next.FFTPV.FapSource
open FFT FFT.IntegerModel MainCertificate MainSuffix MainFinish
open RH080Next.Explicit

/-- The actual C algorithm's exact answer, with its original successive
upward divisions and 20-ulp allowance. Both large numerical leaves come from
accepted kernel proofs of the unchanged complete FFT and quadrature. -/
theorem norm_answer_checked : normAnswer .fap fapCertificate=781796015790084776 := by
  change finishValue true 131072
    (NormalizeSource.totalValue true
      (FFT.Limbs.ceilQuotient (absSum fapCertificate.output) (1000000000^2)) 131072)
    (100*FapForest17.quad)=781796015790084776
  rw [fap_certificate_sum,FapForest17.quad_checked]
  norm_num [finishValue,scalarConvert,NormalizeSource.totalValue,NormalizeSource.quadValue,
    FFT.Limbs.ceilQuotient,AnswerSource.computed,AnswerSource.profileAllowance,
    AnswerSource.limit,AnswerSource.sentinel]

/-- Source characters/independent grammar, actual fixed main callsite, and
actual complete modeled numerical execution are all part of this result.
Physical compiled stdout observations are recorded separately. -/
theorem actual_source_result : SourceOutput.Result .fap 781796015790084776 := by
  have actual:=SourceOutput.actual_result .fap fapCertificate
    (by rw [norm_answer_checked];norm_num [AnswerSource.sentinel])
  simpa only [norm_answer_checked] using actual

/-- Every non-sentinel actual source output satisfies the real periodic-norm
bound. The proof obtains its numerical value from the entire source Call
correctness theorem, not from an assumed output or certificate-checker label. -/
theorem source_output_periodic_norm (out : Nat) (actual : SourceOutput.Result .fap out) :
    (∫ y in (0:ℝ)..1,|nodalPolynomial FapPV.Data.affineNodes y|)≤
      (out:ℝ)/1000000000000000000 := by
  have value:=(SourceOutput.result_value_eq fapCertificate actual).trans norm_answer_checked
  rw [value]
  have h:=RH080Next.Primal.FapFFTKernel.kernel_periodic_norm
  rw [FapForest17.numerator_checked] at h
  exact h

/-- The actual C source's modeled output is consumed in the numerical leaf.
The general BR Fourier identity remains an explicit analytic source input. -/
theorem source_first_actual_norm (hBRNorm : Explicit.SourceBRFourierNormFive) :
    (∫ u : ℝ,|inverseCosine (affineSpectrum FapPV.Data.affineNodes 80) u|)≤
      (7817960157900848:ℝ)/10000000000000000 := by
  rw [hBRNorm FapPV.Data.affineNodes 80 (by norm_num)
    (by simpa using FapPV.Data.affineNodes_length) RH080Next.Primal.FapFFTKernel.actual_terminal]
  exact (source_output_periodic_norm _ actual_source_result).trans (by norm_num)

#print axioms norm_answer_checked
#print axioms actual_source_result
#print axioms source_output_periodic_norm
#print axioms source_first_actual_norm
end RH080Next.FFTPV.FapSource
