import SourceDensityPoly
namespace SynergyAnalytic
open Real Set MeasureTheory WinnerDensitySource
set_option maxHeartbeats 0

noncomputable def stripProduct (UL VR sigma sigma2 shift : ℝ) : ℝ :=
  UL^((sigma2-(sigma-shift))/(sigma2-1/2))*
    VR^(((sigma-shift)-1/2)/(sigma2-1/2))

/-- Retain the exact finite-height three-lines exponents.  The old coarse
density coefficient is not used in this transfer. -/
theorem exact_count_from_source_moments
    {sigma sigma2 H T mu C7 C8 Fdiff Mmid Mleft Mright UL VR omega d alpha R : ℝ}
    (hT : 1 < T) (hd : 0 < d) (hHeight : H < T) (hOmega : 0 < omega)
    (hStripLeft : (1/2:ℝ) ≤ sigma-d/Real.log T)
    (hStripRight : sigma-d/Real.log T ≤ sigma2) (hStripWidth : (1/2:ℝ) < sigma2)
    (hFdiff : 0 ≤ Fdiff) (hML : 0 ≤ Mleft) (hMR : 0 ≤ Mright)
    (hSourceCount : IEANTN.zetaN' sigma T ≤
      ((T-H)*Real.log (1+Fdiff/(T-H))+
        (C7*(mu-(sigma-d/Real.log T))+C8/2)*Real.log T)/
        (2*Real.pi*(sigma-(sigma-d/Real.log T))))
    (hSourceUnsmoothing : Fdiff ≤ Mmid/(2*omega^2))
    (hSourceInterpolation : Mmid ≤
      Mleft^((sigma2-(sigma-d/Real.log T))/(sigma2-1/2))*
        Mright^(((sigma-d/Real.log T)-1/2)/(sigma2-1/2)))
    (hLeft : Mleft ≤ UL) (hRight : Mright ≤ VR)
    (hReciprocal : 1/(2*omega^2) ≤ R*Real.exp (2*alpha)) :
    IEANTN.zetaN' sigma T ≤
      R*Real.exp (2*alpha)*Real.log T/(2*Real.pi*d)*
        stripProduct UL VR sigma sigma2 (d/Real.log T)+
      ((C7*(mu-(sigma-d/Real.log T))+C8/2)/(2*Real.pi*d))*Real.log T^2 := by
  have hl : 0 < Real.log T := Real.log_pos hT
  have hgap : sigma-d/Real.log T < sigma := by
    have hp := div_pos hd hl
    linarith
  have hc := count_of_source_moments hgap hHeight hOmega hStripLeft hStripRight hStripWidth
    hFdiff hML hMR hSourceCount hSourceUnsmoothing hSourceInterpolation hLeft hRight
  let Q : ℝ := stripProduct UL VR sigma sigma2 (d/Real.log T)
  have hQ : 0 ≤ Q := by
    unfold Q stripProduct
    exact mul_nonneg (Real.rpow_nonneg (hML.trans hLeft) _) (Real.rpow_nonneg (hMR.trans hRight) _)
  have hc' : IEANTN.zetaN' sigma T ≤
      ((T-H)*Real.log (1+Q/(2*omega^2*(T-H)))+
        (C7*(mu-(sigma-d/Real.log T))+C8/2)*Real.log T)/
        (2*Real.pi*(sigma-(sigma-d/Real.log T))) := by
    simpa only [Q,stripProduct] using hc
  have hn := count_log_relax hgap hHeight hOmega hQ hc'
  have hm := mul_le_mul_of_nonneg_left hReciprocal hQ
  have hm' := mul_le_mul_of_nonneg_right hm
    (show 0 ≤ Real.log T/(2*Real.pi*d) by positivity)
  have he : (Q/(2*omega^2)+(C7*(mu-(sigma-d/Real.log T))+C8/2)*Real.log T)/
      (2*Real.pi*(sigma-(sigma-d/Real.log T))) =
      (Q*(1/(2*omega^2)))*(Real.log T/(2*Real.pi*d))+
        ((C7*(mu-(sigma-d/Real.log T))+C8/2)/(2*Real.pi*d))*Real.log T^2 := by
    field_simp [hl.ne',hd.ne',Real.pi_ne_zero,hOmega.ne']
    <;> ring
  rw [he] at hn
  dsimp [Q] at hn hm'
  have hf := hn.trans (add_le_add hm' le_rfl)
  convert hf using 1 <;> first | rfl | ring

/-- Exact interpolation is exponential-affine in sigma at each height, even
when the left/right moment caps themselves vary continuously with height. -/
theorem stripProduct_centered
    {UL VR sigma beta sigma2 shift : ℝ} (hUL : 0 < UL) (hVR : 0 < VR)
    (hwidth : sigma2-(1/2:ℝ) ≠ 0) :
    stripProduct UL VR sigma sigma2 shift = stripProduct UL VR beta sigma2 shift*
      Real.exp (((Real.log UL-Real.log VR)/(sigma2-1/2))*(beta-sigma)) := by
  unfold stripProduct
  rw [Real.rpow_def_of_pos hUL,Real.rpow_def_of_pos hVR,
    Real.rpow_def_of_pos hUL,Real.rpow_def_of_pos hVR,
    ← Real.exp_add,← Real.exp_add,← Real.exp_add]
  congr 1
  field_simp
  <;> ring

#print axioms exact_count_from_source_moments
#print axioms stripProduct_centered
end SynergyAnalytic
