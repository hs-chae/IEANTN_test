/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTW4SourceCertificate
import FFTMainIOOutput
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2000000
noncomputable section
open Real MeasureTheory
namespace RH080Next.FFTPV.W4Main
open FFT FFT.IntegerModel MainCertificate MainSuffix MainFinish
open RH080Next.Explicit

theorem norm_answer_checked : normAnswer .w4 w4Certificate=7813568381279800 := by
  suffices h : ∀ c : Certificate .w4,
      absSum c.output = 13108990146528710930483896317271209147027400 →
      W4.quad = 1157537949152935144487960 →
      normAnswer .w4 c = 7813568381279800 by
    exact h w4Certificate w4_certificate_sum W4DAG24.quad_checked
  intro c hsum hquad
  change finishValue false 16777216
    (NormalizeSource.totalValue false
      (FFT.Limbs.ceilQuotient (absSum c.output) (1000000000^2)) 16777216)
    W4.quad=7813568381279800
  rw [hsum,hquad]
  norm_num [finishValue,scalarConvert,NormalizeSource.totalValue,NormalizeSource.quadValue,
    FFT.Limbs.ceilQuotient,AnswerSource.computed,AnswerSource.profileAllowance,
    AnswerSource.limit,AnswerSource.sentinel]

theorem actual_main_result : MainIO.Result .w4 7813568381279800 := by
  have actual:=MainIO.actual_result .w4 w4Certificate
    (by rw [norm_answer_checked];norm_num [AnswerSource.sentinel])
  simpa only [norm_answer_checked] using actual

/-- The exact norm bound consumes the actual complete main execution and
its final printf event. The source-to-integral identity is still explicit. -/
theorem main_output_actual_norm (hBRNorm : SourceBRFourierNormFive)
    (out : Nat) (actual : MainIO.Result .w4 out) :
    (∫ u : ℝ,|inverseCosine (affineSpectrum WindowPV.Data.affineNodes 360) u|)≤
      (out:ℝ)/10000000000000000 := by
  have value:=(MainIO.result_value_eq w4Certificate actual).trans norm_answer_checked
  rw [value]
  have h:=RH080Next.Primal.W4FFTKernel.actual_norm_from_trace24 hBRNorm
    W4DAG24.stages W4DAG24.output W4DAG24.complete_execution W4DAG24.seed W4DAG24.topTail
    (by rw [←W4DAG24.top_shape];exact W4DAG24.length_w24) W4DAG24.decoded_seed_exact
    (by simpa only [W4DAG24.top_shape,List.tail_cons] using W4DAG24.global_twiddle_trace)
    (by intro t ht;rw [←W4DAG24.top_shape];exact W4DAG24.all_stage_chains t ht)
  rw [W4DAG24.numerator_checked] at h
  exact h

theorem source_first_actual_norm (hBRNorm : SourceBRFourierNormFive) :
    (∫ u : ℝ,|inverseCosine (affineSpectrum WindowPV.Data.affineNodes 360) u|)≤
      (7813568381304104:ℝ)/10000000000000000 :=
  (main_output_actual_norm hBRNorm _ actual_main_result).trans (by norm_num)

end RH080Next.FFTPV.W4Main
