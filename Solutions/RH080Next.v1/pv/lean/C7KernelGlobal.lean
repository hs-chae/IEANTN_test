import C7KernelScalars
import W4FFTCertifiedNorm
import ExplicitAnalyticTransfer
import ExplicitProfileResiduals
import ExplicitCMSZeroKernel
import FinitePrimeGapBridge
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2000000
noncomputable section
open Real Set MeasureTheory
namespace RH080Next.PosthocKernelControl
open RH080Next.Explicit RH080Next.FiniteGap

private theorem appended_zero (xs : List ℚ) : node (xs ++ [0]) xs.length = 0 := by
  unfold node
  rw [List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self]
  norm_num

section AnalyticInputs
variable (hBR : SourceBRFourierNormStrip) (hCMS : SourceCMSGuinandWeil)
    (hDigamma : SourceDLMFDigammaIntegral) (hCount : SourceCMSZeroCounting)
    (hEta : SourceDLMFRealEtaIntegral) (hMV : SourceMontgomeryVaughan)
    (hRH : RiemannHypothesis)
include hBR hCMS hDigamma hCount hEta hMV hRH

theorem ray_of_kernel_norm
    (hNorm : (∫ u : ℝ, |inverseCosine (affineSpectrum WindowPV.Data.affineNodes 360) u|) ≤
      (7813568381304104 : ℝ)/10000000000000000)
    (t : ℝ) (ht : 42 ≤ t) :
    ∃ p : ℕ, Nat.Prime p ∧ exp t < (p : ℝ) ∧
      (p : ℝ) < exp t+(425531/500000 : ℝ)*sqrt (exp t)*log (exp t) := by
  obtain ⟨hF, hA, hV0, hV1, hmu, hJ, hH, hW⟩ := scalar_caps
  have hS := w4_signed_cap WindowPV.Data.affineNodes 360 hF hV1 hmu
  let J := IEANTN.CMSFunctional.positiveLeak (affineSpectrum WindowPV.Data.affineNodes 360)
  let H := nodalH WindowPV.Data.affineNodes 360
  let D := nodalF0 WindowPV.Data.affineNodes 360-explicitPenalty*J
  let K := explicitConstant (425531/500000) J H
    (nodalSignedLogUpper WindowPV.Data.affineNodes 360 (3/8)) 1
  have hK : K ≤ 0 := w4_constant_cap _ J H _ hH hS
  have hDcap : (1836193/2000000 : ℝ) ≤ D := w4_denominator_lower _ _ hF hJ
  have hResidual := w4_ray_residual D K t hDcap hK ht
  have hNorm' : (∫ u : ℝ,
      |inverseCosine (affineSpectrum WindowPV.Data.affineNodes 360) u|) ≤
        (19533921/25000000 : ℝ) := hNorm.trans (by norm_num)
  apply actual_prime_interval_of_residual hBR hCMS hDigamma
    cms_zero_partial_summation_kernel hCount hEta hMV hRH
    WindowPV.Data.affineNodes 360 504 (by norm_num) (by norm_num)
    (by rw [WindowPV.Data.affineNodes_length] <;> norm_num)
    (by simpa only [WindowPV.Data.affineNodes, WindowPV.Data.nodes_length] using
      appended_zero WindowPV.Data.nodes)
    (by rw [WindowPV.Data.affineNodes_length] <;> norm_num)
    (by unfold radius; rw [WindowPV.Data.affineNodes_length] <;> norm_num) hA hV0
    (hV1.trans (by norm_num)) (hmu.trans (by norm_num))
    1 (by norm_num) (by norm_num) hW (425531/500000) t 1 (19533921/25000000)
    (by norm_num) (by norm_num) ht (by norm_num) (by norm_num) hNorm' (by norm_num)
    (by change 0 ≤ D; linarith) hResidual

theorem global_of_kernel_norm (hgap : HistoricalFiniteGap)
    (hNorm : (∫ u : ℝ, |inverseCosine (affineSpectrum WindowPV.Data.affineNodes 360) u|) ≤
      (7813568381304104 : ℝ)/10000000000000000)
    (x : ℝ) (hx : 4 ≤ x) :
    ∃ p : ℕ, Nat.Prime p ∧ x < (p : ℝ) ∧
      (p : ℝ) < x+(425531/500000 : ℝ)*sqrt x*log x := by
  by_cases hs : x ≤ exp 42
  · rcases finite_open_08_through_exp42 hgap x hx hs with ⟨p, hp, hlo, hhi⟩
    refine ⟨p, hp, hlo, hhi.trans_le ?_⟩
    have hprod : 0 ≤ sqrt x * log x :=
      mul_nonneg (Real.sqrt_nonneg x) (Real.log_nonneg (by linarith))
    nlinarith
  have hpos : 0 < x := by linarith
  have ht : 42 ≤ log x := by
    have hle : exp 42 ≤ x := le_of_lt (lt_of_not_ge hs)
    have hlog := Real.log_le_log (Real.exp_pos 42) hle
    simpa only [Real.log_exp] using hlog
  simpa only [Real.exp_log hpos] using
    ray_of_kernel_norm hBR hCMS hDigamma hCount hEta hMV hRH hNorm (log x) ht

end AnalyticInputs


theorem matched_fully_kernel_global
    (hBRNorm : SourceBRFourierNormFive) (hBR : SourceBRFourierNormStrip)
    (hCMS : SourceCMSGuinandWeil) (hDigamma : SourceDLMFDigammaIntegral)
    (hCount : SourceCMSZeroCounting) (hEta : SourceDLMFRealEtaIntegral)
    (hMV : SourceMontgomeryVaughan) (hRH : RiemannHypothesis)
    (hgap : HistoricalFiniteGap) (x : ℝ) (hx : 4 ≤ x) :
    ∃ p : ℕ, Nat.Prime p ∧ x < (p : ℝ) ∧
      (p : ℝ) < x+(425531/500000 : ℝ)*sqrt x*log x :=
  global_of_kernel_norm hBR hCMS hDigamma hCount hEta hMV hRH hgap
    (W4DAG24.kernel_actual_norm hBRNorm) x hx


end RH080Next.PosthocKernelControl
