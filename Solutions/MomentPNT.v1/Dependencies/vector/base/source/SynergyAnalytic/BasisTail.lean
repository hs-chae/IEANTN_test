import SynergyAnalytic.Basis
namespace SynergyAnalytic
open Real Set MeasureTheory Filter
set_option maxHeartbeats 0

theorem baseWeight_le_peak {x : ℝ} (hx : 0 < x) : baseWeight x ≤ universalPeak := by
  have he : baseWeight x = Real.exp (baseLog (601/2500) x) := by
    unfold baseWeight baseLog
    rw [Real.rpow_def_of_pos hx,← Real.exp_add]
    congr 1
    ring
  rw [he,universalPeak]
  exact Real.exp_le_exp.mpr (baseLog_le_peak (by norm_num) hx)

theorem peakX_le_five_sixths : peakX ≤ (5/6:ℝ) := by
  unfold peakX
  apply Real.sqrt_le_iff.mpr
  norm_num

/-- A rational cut avoids an unevaluated square root in the numerical program. -/
theorem basisZero_rational_prefix {b : ℝ} (hb : 1 ≤ b) :
    basisZero b ≤ universalPeak*(5/6:ℝ)+∫ x in (5/6:ℝ)..b, baseWeight x := by
  have hi := intervalIntegral.integral_add_adjacent_intervals (μ:=volume)
    (baseWeight_continuous.intervalIntegrable peakX (5/6))
    (baseWeight_continuous.intervalIntegrable (5/6) b)
  have hc : (∫ x in peakX..(5/6:ℝ), baseWeight x) ≤
      universalPeak*((5/6:ℝ)-peakX) := by
    have hm := intervalIntegral.integral_mono_on (μ:=volume) peakX_le_five_sixths
      (baseWeight_continuous.intervalIntegrable peakX (5/6))
      (intervalIntegrable_const (c:=universalPeak))
      (by intro x hx;exact baseWeight_le_peak (peakX_positive.trans_le hx.1))
    simpa [intervalIntegral.integral_const,smul_eq_mul,mul_comm] using hm
  unfold basisZero
  linarith

theorem gaussian_cubic_tail {q c : ℝ} (hq : 0 < q) :
    (∫ x in Ioi c, x^3*Real.exp (-q*x^2)) =
      Real.exp (-q*c^2)*(q*c^2+1)/(2*q^2) := by
  let F : ℝ → ℝ := fun x => -(Real.exp (-q*x^2)*(q*x^2+1)/(2*q^2))
  have hqn : q ≠ 0 := hq.ne'
  have hd : ∀ x : ℝ, HasDerivAt F (x^3*Real.exp (-q*x^2)) x := by
    intro x
    have he := (((((hasDerivAt_id x).pow 2).const_mul (-q)).exp).mul
      ((((hasDerivAt_id x).pow 2).const_mul q).add_const 1)).div_const (2*q^2)
    have hn := he.neg
    convert hn using 1 <;> first | rfl | (norm_num [F];field_simp <;> ring)
  have hi : IntegrableOn (fun x : ℝ => x^3*Real.exp (-q*x^2)) (Ioi c) := by
    have hh := (integrable_rpow_mul_exp_neg_mul_sq hq (s:=3) (by norm_num)).integrableOn (s:=Ioi c)
    simpa only [Real.rpow_ofNat] using hh
  have hz : Tendsto (fun x : ℝ => Real.exp (-(1/2:ℝ)*x)) atTop (nhds 0) := by
    simpa only [Real.rpow_zero,one_mul] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 (1/2) (by norm_num))
  have h0 := (rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg hq 0).tendsto_zero_of_tendsto hz
  have h2 := (rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg hq 2).tendsto_zero_of_tendsto hz
  simp only [Real.rpow_zero,one_mul] at h0
  simp only [Real.rpow_two] at h2
  have hlim : Tendsto F atTop (nhds 0) := by
    have hh := (((h2.const_mul q).add h0).div_const (2*q^2)).neg
    convert hh using 1 <;> first | rfl | (funext x;dsimp [F];ring) | norm_num
  have hc : Continuous F := by dsimp [F];fun_prop
  have hr := integral_Ioi_of_hasDerivAt_of_tendsto hc.continuousAt.continuousWithinAt
    (fun x hx => hd x) hi hlim
  simpa only [F,zero_sub,neg_neg] using hr

theorem log_basis_le_cubic {x : ℝ} (hx : 1 ≤ x) {k : ℕ} (hk : k ≤ 2) :
    baseWeight x*(Real.log x)^k ≤ x^3*Real.exp (-(601/2500:ℝ)*x^2) := by
  have xp : 0 < x := by linarith
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx
  have hlog : Real.log x ≤ x := by linarith [Real.log_le_sub_one_of_pos xp]
  have hpow := pow_le_pow_left₀ hl hlog k
  have hpow' : x^k ≤ x^2 := pow_le_pow_right₀ hx hk
  have hroot : x^((1:ℝ)/3) ≤ x := Real.rpow_le_self_of_one_le hx (by norm_num)
  have hm := mul_le_mul hroot (hpow.trans hpow') (pow_nonneg hl _) xp.le
  have hs := mul_le_mul_of_nonneg_left hm (Real.exp_pos (-(601/2500:ℝ)*x^2)).le
  unfold baseWeight
  nlinarith

#print axioms basisZero_rational_prefix
#print axioms gaussian_cubic_tail
#print axioms log_basis_le_cubic
end SynergyAnalytic
