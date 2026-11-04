/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import SourceDensityK1
import Mathlib.Analysis.Real.Pi.Bounds
open Real
namespace WinnerDensitySource

noncomputable def interpolationPhi (delta U V : ℝ) : ℝ :=
  4/3+(U/V)*Real.exp (-8*delta/3-1)

noncomputable def interpolationCoefficient (sigma d delta U V : ℝ) : ℝ :=
  U^(2*(1-sigma))*V^(2*sigma-1)*
    Real.exp ((2*d+2*delta*(2*sigma-1))*interpolationPhi delta U V)

/-- The new left-line provider and unchanged right-line provider feed the exact
strip interpolation. The universal log estimate has already been proved. -/
theorem interpolation_product_bound {sigma d delta T U V : ℝ}
    (hT : 1 < T) (hdelta : 0 ≤ delta) (hU : 0 < U) (hV : 0 < V)
    (hP : 0 ≤ 2*d+2*delta*(2*sigma-1)) :
    let L := Real.log T
    let a := ((1+delta/L)-(sigma-d/L))/((1+delta/L)-1/2)
    (U*T^(4/3:ℝ)*L^(3:ℕ))^a * (V*L^(2:ℕ))^(1-a) ≤
      interpolationCoefficient sigma d delta U V *
        T^(8*(1-sigma)/3) * L^(4-2*sigma) := by
  dsimp only
  have hT0 : 0 < T := lt_trans zero_lt_one hT
  have hL : 0 < Real.log T := Real.log_pos hT
  have hLeft : 0 < U*T^(4/3:ℝ)*Real.log T^(3:ℕ) := by positivity
  have hRight : 0 < V*Real.log T^(2:ℕ) := by positivity
  have hlLeft : Real.log (U*T^(4/3:ℝ)*Real.log T^(3:ℕ)) =
      Real.log U+3*Real.log (Real.log T)+4*Real.log T/3 := by
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul hU.ne' (by positivity), Real.log_rpow hT0, Real.log_pow]
    ring
  have hlRight : Real.log (V*Real.log T^(2:ℕ)) =
      Real.log V+2*Real.log (Real.log T) := by
    rw [Real.log_mul hV.ne' (by positivity), Real.log_pow]
    norm_num
  rw [Real.rpow_def_of_pos hLeft, Real.rpow_def_of_pos hRight, ← Real.exp_add,
    hlLeft, hlRight, shifted_exponent_identity hL hdelta]
  have hbudget := uniform_interpolation_exponent_budget (sigma:=sigma) (d:=d)
    (delta:=delta) (L:=Real.log T) hL hdelta hU hV hP
  dsimp only at hbudget
  have hh := Real.exp_le_exp.mpr hbudget
  have he1 :
      (Real.log U+3*Real.log (Real.log T)+4*Real.log T/3)*
          (2*(1-sigma)+(2*d+2*delta*(2*sigma-1))/(Real.log T+2*delta))+
        (Real.log V+2*Real.log (Real.log T))*
          (1-(2*(1-sigma)+(2*d+2*delta*(2*sigma-1))/(Real.log T+2*delta))) =
      (2*(1-sigma)+(2*d+2*delta*(2*sigma-1))/(Real.log T+2*delta))*
          (Real.log U+3*Real.log (Real.log T)+4*Real.log T/3)+
        (1-(2*(1-sigma)+(2*d+2*delta*(2*sigma-1))/(Real.log T+2*delta)))*
          (Real.log V+2*Real.log (Real.log T)) := by ring
  rw [he1]
  apply hh.trans_eq
  unfold interpolationCoefficient interpolationPhi
  rw [Real.rpow_def_of_pos hU, Real.rpow_def_of_pos hV,
    Real.rpow_def_of_pos hT0, Real.rpow_def_of_pos hL]
  simp only [← Real.exp_add]
  congr 1
  ring


/-- The reciprocal smoothing factor is kept separate from its source proof. -/
noncomputable def densityCoefficient (sigma d delta alpha U V R : ℝ) : ℝ :=
  (R*Real.exp (2*alpha)/(2*Real.pi*d))*interpolationCoefficient sigma d delta U V

/-- Coarse published boundary errors are tiny relative to the main density term.
The cap is proved, rather than assumed as a new density input. -/
theorem boundary_coefficient_le_six {sigma d L mu C7 C8 : ℝ}
    (hs : (3/4:ℝ) ≤ sigma) (hd : (34/100:ℝ) ≤ d) (hd' : d ≤ 35/100)
    (hL : 28 ≤ L) (hmu : mu ≤ 5/4) (hC7 : 0 ≤ C7) (hC7' : C7 ≤ 20)
    (hC8 : C8 ≤ 1) :
    (C7*(mu-(sigma-d/L))+C8/2)/(2*Real.pi*d) ≤ 6 := by
  have hLp : 0 < L := by linarith
  have hdp : 0 < d := by linarith
  have hdr : d/L ≤ (1/80:ℝ) := by
    apply (div_le_iff₀ hLp).mpr
    nlinarith
  have hr : mu-(sigma-d/L) ≤ (41/80:ℝ) := by linarith
  have hb := mul_le_mul hr hC7' hC7 (by norm_num : (0:ℝ) ≤ 41/80)
  apply (div_le_iff₀ (by positivity : 0 < 2*Real.pi*d)).mpr
  have hpi : (3:ℝ) ≤ Real.pi := Real.pi_gt_three.le
  have hpd := mul_le_mul_of_nonneg_right hpi hdp.le
  nlinarith

/-- Linearize the source logarithm only after its genuine moment bound is available. -/
theorem count_log_relax {sigma sigmap H T Q omega B : ℝ}
    (hGap : sigmap < sigma) (hHeight : H < T) (hOmega : 0 < omega) (hQ : 0 ≤ Q)
    (hc : IEANTN.zetaN' sigma T ≤
      ((T-H)*Real.log (1+Q/(2*omega^2*(T-H)))+B)/(2*Real.pi*(sigma-sigmap))) :
    IEANTN.zetaN' sigma T ≤ (Q/(2*omega^2)+B)/(2*Real.pi*(sigma-sigmap)) := by
  have hD : 0 < T-H := sub_pos.mpr hHeight
  have hArg : 0 < 1+Q/(2*omega^2*(T-H)) := by positivity
  have hl := Real.log_le_sub_one_of_pos hArg
  have hm := mul_le_mul_of_nonneg_left hl hD.le
  have he : (T-H)*(1+Q/(2*omega^2*(T-H))-1) = Q/(2*omega^2) := by
    field_simp
    ring
  rw [he] at hm
  exact hc.trans ((div_le_div_of_nonneg_right (by linarith :
    (T-H)*Real.log (1+Q/(2*omega^2*(T-H)))+B ≤ Q/(2*omega^2)+B)
      (by nlinarith [Real.pi_pos])).trans le_rfl)


/-- The retained coefficient is exactly exponential-affine in the zero cutoff. -/
noncomputable def densitySlope (delta U V : ℝ) : ℝ :=
  2*Real.log (V/U)+4*delta*interpolationPhi delta U V

theorem densityCoefficient_centered {sigma beta d delta alpha U V R : ℝ}
    (hU : 0 < U) (hV : 0 < V) :
    densityCoefficient sigma d delta alpha U V R =
      densityCoefficient beta d delta alpha U V R *
        Real.exp (densitySlope delta U V*(sigma-beta)) := by
  unfold densityCoefficient interpolationCoefficient densitySlope
  rw [Real.log_div hV.ne' hU.ne']
  rw [Real.rpow_def_of_pos hU, Real.rpow_def_of_pos hV,
    Real.rpow_def_of_pos hU, Real.rpow_def_of_pos hV]
  simp only [← Real.exp_add, mul_assoc]
  congr 1
  congr 1
  ring

/-- Checked endpoint and slope bounds dominate the entire cutoff interval. -/
theorem densityCoefficient_model_cap {sigma beta d delta alpha U V R k B : ℝ}
    (hU : 0 < U) (hV : 0 < V) (hd : 0 < d) (hR : 0 ≤ R)
    (hs : sigma ≤ beta)
    (hk : densityCoefficient beta d delta alpha U V R ≤ k)
    (hB : B ≤ densitySlope delta U V) :
    densityCoefficient sigma d delta alpha U V R ≤ k*Real.exp (-B*(beta-sigma)) := by
  rw [densityCoefficient_centered (beta:=beta) hU hV]
  have hc : 0 ≤ densityCoefficient beta d delta alpha U V R := by
    unfold densityCoefficient interpolationCoefficient
    positivity
  have hExp : Real.exp (densitySlope delta U V*(sigma-beta)) ≤
      Real.exp (-B*(beta-sigma)) := by
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonpos_right hB (sub_nonpos.mpr hs)
    nlinarith
  exact mul_le_mul hk hExp (Real.exp_pos _).le (hc.trans hk)

/-- The exact named source relations, the new left moment, and the old right moment
imply the actual strict zero count. No density conclusion is an input. -/
theorem count_poly_of_source_moments
    {sigma H T mu C7 C8 Fdiff Mmid Mleft Mright omega d delta alpha U V R : ℝ}
    (hs : (3/4:ℝ) ≤ sigma) (hs' : sigma ≤ 7/8)
    (hd : (34/100:ℝ) ≤ d) (hd' : d ≤ 35/100)
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
  have hdr : d/Real.log T ≤ (1/80:ℝ) := by
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
  have hBoundary := boundary_coefficient_le_six hs hd hd' hL hmu hC7 hC7' hC8
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

#print axioms interpolation_product_bound
#print axioms boundary_coefficient_le_six
#print axioms count_log_relax
#print axioms densityCoefficient_centered
#print axioms densityCoefficient_model_cap
#print axioms count_poly_of_source_moments
end WinnerDensitySource
