/- Copyright (c) 2026 IEANTN contributors. Released under Apache2.0. -/
import SourceDensityPoly
namespace WinnerNewHeightSource
open Real WinnerDensitySource
set_option maxHeartbeats 0
theorem boundary_coefficient_le_six_extended {sigma d L mu C7 C8 : ℝ}
    (hs : (3/4:ℝ) ≤ sigma) (hd : (34/100:ℝ) ≤ d) (hd' : d ≤ 2/5)
    (hL : 28 ≤ L) (hmu : mu ≤ 5/4) (hC7 : 0 ≤ C7) (hC7' : C7 ≤ 20)
    (hC8 : C8 ≤ 1) :
    (C7*(mu-(sigma-d/L))+C8/2)/(2*Real.pi*d) ≤ 6 := by
  have hLp : 0 < L := by linarith
  have hdp : 0 < d := by linarith
  have hdr : d/L ≤ (1/70:ℝ) := by
    apply (div_le_iff₀ hLp).mpr
    nlinarith
  have hr : mu-(sigma-d/L) ≤ (41/70:ℝ) := by linarith
  have hb := mul_le_mul hr hC7' hC7 (by norm_num : (0:ℝ) ≤ 41/70)
  apply (div_le_iff₀ (by positivity : 0 < 2*Real.pi*d)).mpr
  have hpi : (3:ℝ) ≤ Real.pi := Real.pi_gt_three.le
  have hpd := mul_le_mul_of_nonneg_right hpi hdp.le
  nlinarith

theorem count_poly_of_source_moments_extended
    {sigma H T mu C7 C8 Fdiff Mmid Mleft Mright omega d delta alpha U V R : ℝ}
    (hs : (3/4:ℝ) ≤ sigma) (hs' : sigma ≤ 7/8)
    (hd : (34/100:ℝ) ≤ d) (hd' : d ≤ 2/5)
    (hT : 1 < T) (hL : 28 ≤ Real.log T) (hdelta : 0 ≤ delta)
    (hU : 0 < U) (hV : 0 < V) (hR : 0 ≤ R)
    (hmu : mu ≤ 5/4) (hC7 : 0 ≤ C7) (hC7' : C7 ≤ 20) (hC8 : C8 ≤ 1)
    (hHeight : H < T) (hOmega : 0 < omega)
    (hFdiff : 0 ≤ Fdiff) (hML : 0 ≤ Mleft) (hMR : 0 ≤ Mright)
    (hSourceCount : IEANTN.zetaN' sigma T ≤
      ((T-H)*Real.log (1+Fdiff/(T-H))+
        (C7*(mu-(sigma-d/Real.log T))+C8/2)*Real.log T)/
        (2*Real.pi*(sigma-(sigma-d/Real.log T))))
    (hSourceUnsmoothing : Fdiff ≤ Mmid/(2*omega^2))
    (hSourceInterpolation : Mmid ≤
      Mleft^(((1+delta/Real.log T)-(sigma-d/Real.log T))/((1+delta/Real.log T)-1/2))*
      Mright^(((sigma-d/Real.log T)-1/2)/((1+delta/Real.log T)-1/2)))
    (hLeft : Mleft ≤ U*T^(4/3:ℝ)*Real.log T^(3:ℕ))
    (hRight : Mright ≤ V*Real.log T^(2:ℕ))
    (hOmegaReciprocal : 1/(2*omega^2) ≤ R*Real.exp (2*alpha)) :
    IEANTN.zetaN' sigma T ≤
      densityCoefficient sigma d delta alpha U V R *
        T^(8*(1-sigma)/3)*Real.log T^(5-2*sigma)+6*Real.log T^(2:ℕ) := by
  have hLp : 0 < Real.log T := by linarith
  have hdp : 0 < d := by linarith
  have hdr : d/Real.log T ≤ (1/70:ℝ) := by
    apply (div_le_iff₀ hLp).mpr
    nlinarith
  have hGap : sigma-d/Real.log T < sigma := by
    have := div_pos hdp hLp
    linarith
  have hStripLeft : (1/2:ℝ) ≤ sigma-d/Real.log T := by linarith
  have hdeltaL : 0 ≤ delta/Real.log T := div_nonneg hdelta hLp.le
  have hStripRight : sigma-d/Real.log T ≤ 1+delta/Real.log T := by
    have := div_pos hdp hLp
    linarith
  have hStripWidth : (1/2:ℝ) < 1+delta/Real.log T := by linarith
  let a := ((1+delta/Real.log T)-(sigma-d/Real.log T))/((1+delta/Real.log T)-1/2)
  let Q := (U*T^(4/3:ℝ)*Real.log T^(3:ℕ))^a *
    (V*Real.log T^(2:ℕ))^(1-a)
  have hb : ((sigma-d/Real.log T)-1/2)/((1+delta/Real.log T)-1/2) = 1-a := by
    dsimp [a]
    have hh : (1+delta/Real.log T)-(1/2:ℝ) ≠ 0 := by linarith
    have hden2 : Real.log T+2*delta ≠ 0 := by positivity
    field_simp [hh, hLp.ne', hden2]
    ring_nf
    all_goals field_simp [hden2]
    all_goals ring
  have hCount := count_of_source_moments hGap hHeight hOmega hStripLeft hStripRight
    hStripWidth hFdiff hML hMR hSourceCount hSourceUnsmoothing hSourceInterpolation hLeft hRight
  rw [hb] at hCount
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hLinear := count_log_relax hGap hHeight hOmega hQ hCount
  have hP : 0 ≤ 2*d+2*delta*(2*sigma-1) := by
    have := mul_nonneg hdelta (show 0 ≤ 2*sigma-1 by linarith)
    linarith
  have hQBound : Q ≤ interpolationCoefficient sigma d delta U V *
      T^(8*(1-sigma)/3)*Real.log T^(4-2*sigma) :=
    interpolation_product_bound hT hdelta hU hV hP
  have hCoeff : 0 ≤ interpolationCoefficient sigma d delta U V := by
    unfold interpolationCoefficient
    positivity
  have hT0 : 0 < T := lt_trans zero_lt_one hT
  have hProd : Q/(2*omega^2) ≤ R*Real.exp (2*alpha)*
      (interpolationCoefficient sigma d delta U V*T^(8*(1-sigma)/3)*
        Real.log T^(4-2*sigma)) := by
    calc Q/(2*omega^2) = Q*(1/(2*omega^2)) := by ring
         _ ≤ (interpolationCoefficient sigma d delta U V*T^(8*(1-sigma)/3)*
            Real.log T^(4-2*sigma))*(R*Real.exp (2*alpha)) :=
           mul_le_mul hQBound hOmegaReciprocal (by positivity) (by positivity)
         _ = _ := by ring
  have hBoundary := boundary_coefficient_le_six_extended hs hd hd' hL hmu hC7 hC7' hC8
  have hDen : 0 < 2*Real.pi*(sigma-(sigma-d/Real.log T)) := by
    have := sub_pos.mpr hGap
    positivity
  have hAdd := div_le_div_of_nonneg_right (by linarith :
      Q/(2*omega^2)+(C7*(mu-(sigma-d/Real.log T))+C8/2)*Real.log T ≤
      R*Real.exp (2*alpha)*(interpolationCoefficient sigma d delta U V*
        T^(8*(1-sigma)/3)*Real.log T^(4-2*sigma))+
        (C7*(mu-(sigma-d/Real.log T))+C8/2)*Real.log T) hDen.le
  apply hLinear.trans (hAdd.trans _)
  have hExp : Real.log T^(5-2*sigma) = Real.log T^(4-2*sigma)*Real.log T := by
    rw [show (5:ℝ)-2*sigma=(4-2*sigma)+1 by ring,Real.rpow_add hLp,Real.rpow_one]
  have hAlg :
      (R*Real.exp (2*alpha)*(interpolationCoefficient sigma d delta U V*
        T^(8*(1-sigma)/3)*Real.log T^(4-2*sigma))+
        (C7*(mu-(sigma-d/Real.log T))+C8/2)*Real.log T)/
          (2*Real.pi*(sigma-(sigma-d/Real.log T))) =
      densityCoefficient sigma d delta alpha U V R*T^(8*(1-sigma)/3)*
        Real.log T^(5-2*sigma)+
      ((C7*(mu-(sigma-d/Real.log T))+C8/2)/(2*Real.pi*d))*Real.log T^(2:ℕ) := by
    rw [hExp]
    unfold densityCoefficient
    field_simp [hLp.ne', hdp.ne', Real.pi_ne_zero]
    ring
  rw [hAlg]
  have hbMul := mul_le_mul_of_nonneg_right hBoundary (sq_nonneg (Real.log T))
  linarith

#print axioms count_poly_of_source_moments_extended
end WinnerNewHeightSource
