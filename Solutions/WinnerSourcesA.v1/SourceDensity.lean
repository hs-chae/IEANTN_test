/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Vocabulary.Zeta
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

open Real MeasureTheory Set
namespace WinnerDensitySource

/-- The original raw Minkowski expression in KLN proof of Lemma4.2, before C4. -/
noncomputable def rawMinkowski (a1 a2 m1 m2 X t : ℝ) : ℝ :=
  ((a1*t^(1/6:ℝ)*Real.log t+a2)*Real.sqrt ((m1*t+m2*X)*Real.log X)+Real.sqrt t)^2

noncomputable def gaussianWeight (alpha x : ℝ) : ℝ :=
  x*Real.exp (-2*alpha*x^2)

/-- KLN Lemma4.5 plus its older raw pointwise bound implies the unrelaxed integral.
The functions F/M represent the actual source mean/smoothed moments in applications.
This generic lemma is not a new density hypothesis or a completed source instantiation. -/
theorem left_moment_of_raw
    (F : ℝ → ℝ) {a1 a2 m1 m2 X T alpha omega Mleft : ℝ}
    (halpha : 0 ≤ alpha) (hT : 0 < T)
    (hSourceSmoothing : Mleft ≤ 8*alpha*omega^2*
      ∫ x in Set.Ioi (0:ℝ), gaussianWeight alpha x*F (x*T))
    (hSourceRaw : ∀ t : ℝ, 0 < t → F t ≤ rawMinkowski a1 a2 m1 m2 X t)
    (hFi : IntegrableOn (fun x : ℝ => gaussianWeight alpha x*F (x*T)) (Set.Ioi 0))
    (hRawi : IntegrableOn (fun x : ℝ => gaussianWeight alpha x*
      rawMinkowski a1 a2 m1 m2 X (x*T)) (Set.Ioi 0)) :
    Mleft ≤ 8*alpha*omega^2*
      ∫ x in Set.Ioi (0:ℝ), gaussianWeight alpha x*rawMinkowski a1 a2 m1 m2 X (x*T) := by
  apply hSourceSmoothing.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply setIntegral_mono_on hFi hRawi measurableSet_Ioi
  intro x hx
  exact mul_le_mul_of_nonneg_left (hSourceRaw (x*T) (mul_pos hx hT))
    (by unfold gaussianWeight; exact mul_nonneg hx.le (Real.exp_pos _).le)

/-- The executable integral certificate is consumed after the source reduction. -/
theorem left_moment_of_integral_certificate
    (F : ℝ → ℝ) {a1 a2 m1 m2 X T alpha omega Mleft I Ubound : ℝ}
    (halpha : 0 ≤ alpha) (hT : 0 < T)
    (hSourceSmoothing : Mleft ≤ 8*alpha*omega^2*
      ∫ x in Set.Ioi (0:ℝ), gaussianWeight alpha x*F (x*T))
    (hSourceRaw : ∀ t : ℝ, 0 < t → F t ≤ rawMinkowski a1 a2 m1 m2 X t)
    (hFi : IntegrableOn (fun x : ℝ => gaussianWeight alpha x*F (x*T)) (Set.Ioi 0))
    (hRawi : IntegrableOn (fun x : ℝ => gaussianWeight alpha x*
      rawMinkowski a1 a2 m1 m2 X (x*T)) (Set.Ioi 0))
    (hIntegralCertificate : (∫ x in Set.Ioi (0:ℝ), gaussianWeight alpha x*
      rawMinkowski a1 a2 m1 m2 X (x*T)) ≤ I)
    (hBudget : 8*alpha*omega^2*I ≤ Ubound) : Mleft ≤ Ubound := by
  have hraw := left_moment_of_raw F halpha hT hSourceSmoothing hSourceRaw hFi hRawi
  exact hraw.trans ((mul_le_mul_of_nonneg_left hIntegralCertificate (by positivity)).trans hBudget)

/-- Exact source Littlewood/Jensen reduction, abstracted only before the new moment estimate.
`hSourceCount` is KLN(2.3)+(2.9) with its source boundary errors; its target is actual zetaN'.
The bounds hLeft/hRight must be proved by genuine source/numerical providers in a final consumer. -/
theorem count_of_source_moments
    {sigma sigmap sigma2 H T mu C7 C8 Fdiff Mmid Mleft Mright UL VR omega : ℝ}
    (hGap : sigmap < sigma) (hHeight : H < T) (hOmega : 0 < omega)
    (hStripLeft : (1/2:ℝ) ≤ sigmap) (hStripRight : sigmap ≤ sigma2)
    (hStripWidth : (1/2:ℝ) < sigma2)
    (hFdiff : 0 ≤ Fdiff) (hML : 0 ≤ Mleft) (hMR : 0 ≤ Mright)
    (hSourceCount : IEANTN.zetaN' sigma T ≤
      ((T-H)*Real.log (1+Fdiff/(T-H))+
        (C7*(mu-sigmap)+C8/2)*Real.log T)/(2*Real.pi*(sigma-sigmap)))
    (hSourceUnsmoothing : Fdiff ≤ Mmid/(2*omega^2))
    (hSourceInterpolation : Mmid ≤
      Mleft^((sigma2-sigmap)/(sigma2-1/2))*Mright^((sigmap-1/2)/(sigma2-1/2)))
    (hLeft : Mleft ≤ UL) (hRight : Mright ≤ VR) :
    IEANTN.zetaN' sigma T ≤
      ((T-H)*Real.log (1+
        (UL^((sigma2-sigmap)/(sigma2-1/2))*VR^((sigmap-1/2)/(sigma2-1/2)))/
          (2*omega^2*(T-H)))+
        (C7*(mu-sigmap)+C8/2)*Real.log T)/(2*Real.pi*(sigma-sigmap)) := by
  have hD : 0 < T-H := sub_pos.mpr hHeight
  have hW : 0 < sigma2-(1/2:ℝ) := sub_pos.mpr hStripWidth
  have ha : 0 ≤ (sigma2-sigmap)/(sigma2-1/2) := div_nonneg (sub_nonneg.mpr hStripRight) hW.le
  have hb : 0 ≤ (sigmap-1/2)/(sigma2-1/2) := div_nonneg (sub_nonneg.mpr hStripLeft) hW.le
  have hmid : Mmid ≤
      UL^((sigma2-sigmap)/(sigma2-1/2))*VR^((sigmap-1/2)/(sigma2-1/2)) := by
    apply hSourceInterpolation.trans
    exact mul_le_mul (Real.rpow_le_rpow hML hLeft ha) (Real.rpow_le_rpow hMR hRight hb)
      (Real.rpow_nonneg hMR _) (Real.rpow_nonneg (hML.trans hLeft) _)
  have hdiff : Fdiff ≤
      (UL^((sigma2-sigmap)/(sigma2-1/2))*VR^((sigmap-1/2)/(sigma2-1/2)))/(2*omega^2) :=
    hSourceUnsmoothing.trans (div_le_div_of_nonneg_right hmid (by positivity))
  have harg : 0 < 1+Fdiff/(T-H) := by
    have := div_nonneg hFdiff hD.le
    linarith
  have hlog : Real.log (1+Fdiff/(T-H)) ≤ Real.log (1+
      (UL^((sigma2-sigmap)/(sigma2-1/2))*VR^((sigmap-1/2)/(sigma2-1/2)))/
        (2*omega^2*(T-H))) := by
    apply Real.log_le_log harg
    calc _ ≤ 1+((UL^((sigma2-sigmap)/(sigma2-1/2))*VR^((sigmap-1/2)/(sigma2-1/2)))/
        (2*omega^2))/(T-H) := by gcongr
         _ = _ := by rw [div_div]
  apply hSourceCount.trans
  apply div_le_div_of_nonneg_right _ (by nlinarith [Real.pi_pos])
  have hm := mul_le_mul_of_nonneg_left hlog hD.le
  linarith

#print axioms left_moment_of_raw
#print axioms left_moment_of_integral_certificate
#print axioms count_of_source_moments
end WinnerDensitySource
