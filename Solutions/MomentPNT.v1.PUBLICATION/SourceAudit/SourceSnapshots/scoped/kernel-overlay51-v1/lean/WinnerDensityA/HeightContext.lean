/- Copyright (c) 2026 IEANTN contributors. Released under Apache2.0. -/
import WinnerDensityA.SourceContext
import WinnerBetaA.DirectHeightMoment
import HeightCountProof
import EulerGammaBound
import ReversAmplitude
namespace WinnerNewHeightSource
open Real Set MeasureTheory
open WinnerOriginalScalars WinnerBetaA.ActualObject WinnerBetaA.HeightSource WinnerDensitySource
set_option maxHeartbeats 0
noncomputable def alpha : ℝ := 601/5000
noncomputable def Hstar : ℝ := height-1
noncomputable def shifted (d sigma T : ℝ) : ℝ := sigma-d/log T
noncomputable def rightLine (delta T : ℝ) : ℝ := 1+delta/log T
noncomputable def sourceOmega (d sigma T : ℝ) : ℝ :=
  (1-1/Hstar)*exp (alpha*((shifted d sigma T)/T)^2-alpha)
noncomputable def sourceFdiff (d sigma T : ℝ) : ℝ :=
  cumulativeSquare T (shifted d sigma T) T-cumulativeSquare T (shifted d sigma T) Hstar

/-- Actual independently sourced relations, before every chosen height-profile
U/V/count cap. Both left mean-square and right source operands retain exact T. -/
structure NewInputs (d delta : ℝ) : Prop where
  lowZeta : ∀u:ℝ,0≤u→u≤3→‖riemannZeta (vertical (1/2) u)‖≤(1461/1000:ℝ)
  reversZeta : ∀u:ℝ,3≤u→‖riemannZeta (vertical (1/2) u)‖≤(611/1000)*u^((1:ℝ)/6)*log u
  mollifierMeanSquare : ∀T:ℝ,height≤T→∀t>0,
    (∫u in (0:ℝ)..t,‖mollifier T (vertical (1/2) u)‖^2)≤(meanOne T*t+meanTwo T*T)*log T
  sourceSmoothing : ∀T:ℝ,height≤T→sourceMoment T (1/2)≤
    (8*(601/5000:ℝ)*exp ((601/5000:ℝ)/(2*T^2)))*
      (∫x in Ioi 0,WinnerBetaA.Minkowski.gaussianWeight x*scaledCriticalF T x)
  sourceRightMoment : ∀T:ℝ,height≤T→sourceMoment T (rightLine delta T)≤
    rightVExact eulerMascheroniConstant delta T*log T^(2:ℕ)
  sourceCount : IEANTN.RiemannHypothesisUpTo height→∀sigma:ℝ,
    (3/4:ℝ)≤sigma→sigma≤7/8→∃E:Set ℝ,E.Countable ∧ ∀T:ℝ,height≤T→T∉E→
      IEANTN.zetaN' sigma T≤
        ((T-Hstar)*log (1+sourceFdiff d sigma T/(T-Hstar))+
          (sourceCSeven eulerMascheroniConstant*((1237/1000:ℝ)-shifted d sigma T)+
            sourceCEight eulerMascheroniConstant/2)*log T)/(2*Real.pi*(sigma-shifted d sigma T))
  sourceUnsmoothing : ∀sigma T:ℝ,(3/4:ℝ)≤sigma→sigma≤7/8→height≤T→
    sourceFdiff d sigma T≤sourceMoment T (shifted d sigma T)/(2*sourceOmega d sigma T^2)
  sourceInterpolation : ∀sigma T:ℝ,(3/4:ℝ)≤sigma→sigma≤7/8→height≤T→
    sourceMoment T (shifted d sigma T)≤
      sourceMoment T (1/2)^((rightLine delta T-shifted d sigma T)/(rightLine delta T-1/2))*
      sourceMoment T (rightLine delta T)^((shifted d sigma T-1/2)/(rightLine delta T-1/2))

theorem actual_Fdiff_nonneg {d sigma T:ℝ} (hd:0<d) (hs:sigma≤7/8) (hT:height≤T) :
    0≤sourceFdiff d sigma T := by
  have hTp : 0<T := lt_of_lt_of_le (by norm_num [height]) hT
  have hLp : 0<log T := log_pos (lt_of_lt_of_le (by norm_num [height]) hT)
  have hsne : shifted d sigma T≠1 := by
    unfold shifted
    have hh := div_pos hd hLp
    linarith
  have hc : Continuous (fun u:ℝ=>‖mollifiedError T (vertical (shifted d sigma T) u)‖^2) :=
    (WinnerSourceContext.vertical_error_continuous hsne T).norm.pow 2
  have hi := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ:=volume) 0 Hstar) (hc.intervalIntegrable (μ:=volume) Hstar T)
  have hp : 0≤∫u in Hstar..T,‖mollifiedError T (vertical (shifted d sigma T) u)‖^2 := by
    apply intervalIntegral.integral_nonneg_of_forall
    · unfold Hstar
      linarith
    · intro u
      positivity
  unfold sourceFdiff cumulativeSquare
  linarith

theorem sourceOmega_pos (d sigma T:ℝ) : 0<sourceOmega d sigma T := by
  have hb : 0<1-1/Hstar := by norm_num [Hstar,height]
  exact mul_pos hb (exp_pos _)

theorem sourceOmega_reciprocal (d sigma T:ℝ) :
    1/(2*sourceOmega d sigma T^2)≤sourceSmoothingR*exp (2*alpha) := by
  have hb : 0<1-1/Hstar := by norm_num [Hstar,height]
  have ha : 0≤alpha*((shifted d sigma T)/T)^2 := by unfold alpha;positivity
  have he : exp (-alpha)≤exp (alpha*((shifted d sigma T)/T)^2-alpha) := exp_le_exp.mpr (by linarith)
  have ho : (1-1/Hstar)*exp (-alpha)≤sourceOmega d sigma T := mul_le_mul_of_nonneg_left he hb.le
  have hp : 0<(1-1/Hstar)*exp (-alpha) := by positivity
  have hs : 2*((1-1/Hstar)*exp (-alpha))^2≤2*sourceOmega d sigma T^2 := by
    have hh := (sq_le_sq₀ hp.le (sourceOmega_pos d sigma T).le).mpr ho
    linarith
  have hh := one_div_le_one_div_of_le (by positivity : 0<2*((1-1/Hstar)*exp (-alpha))^2) hs
  apply hh.trans_eq
  rw [mul_pow,←exp_nat_mul]
  rw [show (2:ℕ)*(-alpha)=-(2*alpha) by norm_num,exp_neg]
  unfold sourceSmoothingR Hstar
  field_simp
  <;> ring

/-- The actual left moment is derived from exact mean-square, a chosen anchor,
signed-log normalization and the concrete kernel provider. No U moment premise. -/
theorem actual_left_from_certificate {d delta A T M1 M2 hbar r0 r1 J U omegaBar:ℝ}
    (h:NewInputs d delta) (hAH:height≤A) (hAT:A≤T)
    (hM1:meanOne A≤M1) (hM2:meanTwo A≤M2) (hh:0<hbar) (hhA:hbar≤log A)
    (hr0:(281/100:ℝ)/((611/1000)*A^((1:ℝ)/6)*log A)≤r0)
    (hr1:1/((611/1000:ℝ)*A^((1:ℝ)/6)*log A*sqrt (log A))≤r1)
    (hKernel:Integrable (WinnerBetaA.SignedHeight.kernel M1 M2 hbar r0 r1))
    (hBudget:(∫y,WinnerBetaA.SignedHeight.kernel M1 M2 hbar r0 r1 y)≤J)
    (hOmega:exp ((601/5000:ℝ)/(2*A^2))≤omegaBar)
    (hNum:8*(601/5000:ℝ)*omegaBar*(611/1000)^2*J≤U) :
    sourceMoment T (1/2)≤U*T^((4:ℝ)/3)*log T^3 := by
  have hA:1<A := lt_of_lt_of_le (by norm_num [height]) hAH
  have hT:1<T := hA.trans_le hAT
  have hTH:height≤T := hAH.trans hAT
  have hMean := mean_square_anchor hA hAT (h.mollifierMeanSquare T hTH)
  have hRaw := raw_from_mean (by linarith : 0<T) (by norm_num : (0:ℝ)≤611/1000)
    Revers.amplitude_floor_upper h.lowZeta h.reversZeta hMean
  have hDom := WinnerBetaA.DirectHeightMoment.raw_log_majorized
    (by norm_num : (0:ℝ)<611/1000) (by norm_num : (0:ℝ)≤281/100)
    (meanOne_nonneg hA) (meanTwo_nonneg hA) (by norm_num : (0:ℝ)≤1461/1000)
    Revers.amplitude_floor_upper hA hAT hM1 hM2 hh hhA hr0 hr1 hRaw
  exact WinnerBetaA.DirectHeightMoment.uniform_left (by norm_num) hA hAT
    (scaledCriticalF_continuous T) (fun x hx=>scaledCriticalF_nonneg (by linarith) hx.le)
    hDom hKernel hBudget hOmega hNum (h.sourceSmoothing T hTH)

theorem actual_right_from_certificate {d delta A T V:ℝ}
    (h:NewInputs d delta) (hd:0<delta) (hAH:height≤A) (hAT:A≤T)
    (hNum:rightV (289/500) delta A≤V) :
    sourceMoment T (rightLine delta T)≤V*log T^(2:ℕ) := by
  have hA:1<A := lt_of_lt_of_le (by norm_num [height]) hAH
  have hT:1<T := hA.trans_le hAT
  have hTH:height≤T := hAH.trans hAT
  have hg := WinnerEulerGamma.euler_gamma_upper
  have hg1 : eulerMascheroniConstant≤1 := by linarith
  have hv := (rightVExact_le hg1 hd hT).trans
    ((rightV_uniform_to hg (by norm_num : (0:ℝ)≤289/500) hd hA hAT).trans hNum)
  exact (h.sourceRightMoment T hTH).trans (mul_le_mul_of_nonneg_right hv (sq_nonneg _))

/-- A concrete source-linked kernel certificate consists of actual real scalar
operands and their executed enclosures, not the desired moment bound. -/
structure KernelCertificate (A U:ℝ) where
  M1 : ℝ
  M2 : ℝ
  hbar : ℝ
  r0 : ℝ
  r1 : ℝ
  J : ℝ
  omegaBar : ℝ
  mean_one : meanOne A≤M1
  mean_two : meanTwo A≤M2
  log_pos : 0<hbar
  log_lower : hbar≤log A
  ratio_zero : (281/100:ℝ)/((611/1000)*A^((1:ℝ)/6)*log A)≤r0
  ratio_one : 1/((611/1000:ℝ)*A^((1:ℝ)/6)*log A*sqrt (log A))≤r1
  kernel_integrable : Integrable (WinnerBetaA.SignedHeight.kernel M1 M2 hbar r0 r1)
  kernel_budget : (∫y,WinnerBetaA.SignedHeight.kernel M1 M2 hbar r0 r1 y)≤J
  omega_upper : exp ((601/5000:ℝ)/(2*A^2))≤omegaBar
  finite_U : 8*(601/5000:ℝ)*omegaBar*(611/1000)^2*J≤U

theorem actual_left {d delta A T U:ℝ} (h:NewInputs d delta)
    (hAH:height≤A) (hAT:A≤T) (c:KernelCertificate A U) :
    sourceMoment T (1/2)≤U*T^((4:ℝ)/3)*log T^3 :=
  actual_left_from_certificate h hAH hAT c.mean_one c.mean_two c.log_pos c.log_lower
    c.ratio_zero c.ratio_one c.kernel_integrable c.kernel_budget c.omega_upper c.finite_U

private theorem count_regular {d delta A T U V k B sigma:ℝ}
    (h:NewInputs d delta) (hd:(34/100:ℝ)≤d) (hdmax:d≤2/5) (hdelta:0<delta)
    (hAH:height≤A) (hAT:A≤T) (hU:0<U) (hV:0<V)
    (c:KernelCertificate A U) (hRight:rightV (289/500) delta A≤V)
    (hK:densityCoefficient (7/8) d delta alpha U V sourceSmoothingR≤k)
    (hB:B≤densitySlope delta U V) (hs:(3/4:ℝ)≤sigma) (hs':sigma≤7/8)
    (hRegular:IEANTN.zetaN' sigma T≤
      ((T-Hstar)*log (1+sourceFdiff d sigma T/(T-Hstar))+
        (sourceCSeven eulerMascheroniConstant*((1237/1000:ℝ)-shifted d sigma T)+
          sourceCEight eulerMascheroniConstant/2)*log T)/(2*Real.pi*(sigma-shifted d sigma T))) :
    IEANTN.zetaN' sigma T≤k*exp (-B*(7/8-sigma))*
      T^(8*(1-sigma)/3)*log T^(5-2*sigma)+6*log T^(2:ℕ) := by
  have hTH:height≤T := hAH.trans hAT
  have hTp:0<T := lt_of_lt_of_le (by norm_num [height]) hTH
  have hL:28≤log T := source_log_height_uniform hTH
  have hLp:0<log T := by linarith
  have hT1:1<T := (log_pos_iff hTp.le).mp hLp
  have hdp:0<d := by linarith
  have hHeight:Hstar<T := by unfold Hstar;linarith
  have hGap:0<sigma-shifted d sigma T := by unfold shifted;have hh:=div_pos hdp hLp;linarith
  have hMu:0≤(1237/1000:ℝ)-shifted d sigma T := by
    unfold shifted
    have hh:=div_nonneg hdp.le hLp.le
    linarith
  have hCount:IEANTN.zetaN' sigma T≤
      ((T-Hstar)*log (1+sourceFdiff d sigma T/(T-Hstar))+
        (20*((1237/1000:ℝ)-shifted d sigma T)+(1:ℝ)/2)*log T)/
        (2*Real.pi*(sigma-shifted d sigma T)) := by
    apply hRegular.trans
    apply div_le_div_of_nonneg_right _ (by positivity)
    have hSeven:=mul_le_mul_of_nonneg_right source_cseven_upper hMu
    have hEight:=source_ceight_upper
    have hb:sourceCSeven eulerMascheroniConstant*((1237/1000:ℝ)-shifted d sigma T)+
        sourceCEight eulerMascheroniConstant/2≤20*((1237/1000:ℝ)-shifted d sigma T)+1/2 := by linarith
    have hh:=mul_le_mul_of_nonneg_right hb hLp.le
    linarith
  have hLeft:=actual_left h hAH hAT c
  have hRightM:=actual_right_from_certificate h hdelta hAH hAT hRight
  have hPoly:=count_poly_of_source_moments_extended hs hs' hd hdmax hT1 hL hdelta.le hU hV
    (by unfold sourceSmoothingR;positivity)
    (by norm_num : (1237/1000:ℝ)≤5/4) (by norm_num : (0:ℝ)≤20)
    (by norm_num : (20:ℝ)≤20) (by norm_num : (1:ℝ)≤1)
    hHeight (sourceOmega_pos d sigma T) (actual_Fdiff_nonneg hdp hs' hTH)
    (WinnerSourceContext.sourceMoment_nonneg T (1/2))
    (WinnerSourceContext.sourceMoment_nonneg T (rightLine delta T))
    hCount (h.sourceUnsmoothing sigma T hs hs' hTH) (h.sourceInterpolation sigma T hs hs' hTH)
    hLeft hRightM (sourceOmega_reciprocal d sigma T)
  have hCap:=densityCoefficient_model_cap hU hV hdp
    (show 0≤sourceSmoothingR by unfold sourceSmoothingR;positivity) hs' hK hB
  have hm:=mul_le_mul_of_nonneg_right hCap
    (show 0≤T^(8*(1-sigma)/3)*log T^(5-2*sigma) by positivity)
  exact hPoly.trans (by nlinarith)

/-- A real height-profile actual-count provider. Chosen U and count bounds are
conclusions: finite scalar/kernel certificates feed source moments, then the
source count/interpolation relations, then a proved all-height extension. -/
theorem count_at_anchor {d delta A T U V k B sigma:ℝ}
    (h:NewInputs d delta) (hd:(34/100:ℝ)≤d) (hdmax:d≤2/5) (hdelta:0<delta)
    (hAH:height≤A) (hAT:A≤T) (hU:0<U) (hV:0<V)
    (c:KernelCertificate A U) (hRight:rightV (289/500) delta A≤V)
    (hK:densityCoefficient (7/8) d delta alpha U V sourceSmoothingR≤k)
    (hB:B≤densitySlope delta U V) (hRH:IEANTN.RiemannHypothesisUpTo height)
    (hs:(3/4:ℝ)≤sigma) (hs':sigma≤7/8) :
    IEANTN.zetaN' sigma T≤k*exp (-B*(7/8-sigma))*
      T^(8*(1-sigma)/3)*log T^(5-2*sigma)+6*log T^(2:ℕ) := by
  obtain ⟨E,hE,hRegular⟩:=h.sourceCount hRH sigma hs hs'
  have hTH:height≤T:=hAH.trans hAT
  have hTp:0<T:=lt_of_lt_of_le (by norm_num [height]) hTH
  have hLp:0<log T:=by linarith [source_log_height_uniform hTH]
  have hQ:ContinuousAt (fun u:ℝ=>k*exp (-B*(7/8-sigma))*u^(8*(1-sigma)/3)*log u^(5-2*sigma)+6*log u^(2:ℕ)) T := by
    have hp:ContinuousAt (fun u:ℝ=>u^(8*(1-sigma)/3)) T:=continuousAt_id.rpow_const (Or.inl hTp.ne')
    have hl:ContinuousAt (fun u:ℝ=>log u) T:=continuousAt_log hTp.ne'
    have hq:ContinuousAt (fun u:ℝ=>log u^(5-2*sigma)) T:=hl.rpow_const (Or.inl hLp.ne')
    exact ((continuousAt_const.mul hp).mul hq).add ((hl.pow 2).const_mul 6)
  apply WinnerExceptionalDensity.zetaN_extend hE hAT hQ
  intro u hu hnot
  exact count_regular h hd hdmax hdelta hAH hu hU hV c hRight hK hB hs hs'
    (hRegular u (hAH.trans hu) hnot)

#print axioms actual_left
#print axioms count_at_anchor

#print axioms actual_left_from_certificate
#print axioms actual_right_from_certificate
end WinnerNewHeightSource
