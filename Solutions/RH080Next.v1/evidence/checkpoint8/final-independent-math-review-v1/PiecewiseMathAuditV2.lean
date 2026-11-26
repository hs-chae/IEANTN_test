import FFTFapMainConsumers
import Lean
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open Real MeasureTheory
namespace IndependentFinalMathReview
open RH080Next.Explicit RH080Next.ExplicitProfiles RH080Next.FiniteGap

def reviewWidth (x : ℝ) : ℝ :=
  if x < 11 then 777/1000 else
  if x ≤ exp 63 then 37/50 else
  if x ≤ exp 70 then 3/4 else
  if x ≤ exp 174 then 4/5 else 425531/500000

/-- Independent reconstruction of the exact five real branches from the
already accepted mathematical APIs, with the W4 norm honestly still explicit. -/
theorem exact_piecewise_from_current_math
    (hNorm : SourceBRFourierNormFive) (hBR : SourceBRFourierNormStrip)
    (hCMS : SourceCMSGuinandWeil) (hD : SourceDLMFDigammaIntegral)
    (hCount : SourceCMSZeroCounting) (hEta : SourceDLMFRealEtaIntegral)
    (hMV : SourceMontgomeryVaughan) (hRH : RiemannHypothesis) (hgap : HistoricalFiniteGap)
    (hn : (∫ u : ℝ, |inverseCosine (affineSpectrum w4Nodes 360) u|) ≤ w4OriginalNormCap)
    (x : ℝ) (hx : 4 ≤ x) :
    ∃ p : ℕ, Nat.Prime p ∧ x < (p:ℝ) ∧ (p:ℝ) < x+reviewWidth x*sqrt x*log x := by
  by_cases h11 : x < 11
  · simpa only [reviewWidth, if_pos h11] using direct_small_0777 x hx h11
  have h11' : 11 ≤ x := le_of_not_gt h11
  by_cases h63 : x ≤ exp 63
  · simpa only [reviewWidth, if_neg h11, if_pos h63] using
      RH080Next.FFTPV.FapMain.source_fap_074_full hNorm hBR hCMS hD hCount hEta hMV hRH hgap x h11' h63
  by_cases h70 : x ≤ exp 70
  · simpa only [reviewWidth, if_neg h11, if_neg h63, if_pos h70] using
      RH080Next.FFTPV.FapMain.source_fap_075_full hNorm hBR hCMS hD hCount hEta hMV hRH hgap x h11' h70
  by_cases h174 : x ≤ exp 174
  · simpa only [reviewWidth, if_neg h11, if_neg h63, if_neg h70, if_pos h174] using
      RH080Next.FFTPV.FapMain.source_fap_08_full hNorm hBR hCMS hD hCount hEta hMV hRH hgap x hx h174
  · simpa only [reviewWidth, if_neg h11, if_neg h63, if_neg h70, if_neg h174] using
      w4_global_full_kernel_of_norm hBR hCMS hD hCount hEta hMV hRH hgap hn x hx

#print axioms exact_piecewise_from_current_math
#check exact_piecewise_from_current_math
end IndependentFinalMathReview

open Lean Elab Command
run_cmd do
  let axioms ← collectAxioms `IndependentFinalMathReview.exact_piecewise_from_current_math
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  unless axioms.all allowed.contains do throwError "Unexpected independent piecewise axiom: {axioms}"
  logInfo "INDEPENDENT_EXACT_PIECEWISE_STD3_PASS"
