import SynergyAnalytic.Weight

namespace SynergyAnalytic
open Real Set
set_option maxHeartbeats 0

noncomputable def baseLog (q x : ℝ) : ℝ := -q*x^2 + Real.log x/3
noncomputable def peakLog (q : ℝ) : ℝ := (-1-Real.log (6*q))/6

/-- The Gaussian times cube-root factor has an exact global peak. -/
theorem baseLog_le_peak {q x : ℝ} (hq : 0 < q) (hx : 0 < x) :
    baseLog q x ≤ peakLog q := by
  have hp : 0 < 6*q := by positivity
  have he := Real.log_le_sub_one_of_pos (mul_pos hp (sq_pos_of_pos hx))
  rw [Real.log_mul hp.ne' (pow_ne_zero 2 hx.ne'), Real.log_pow] at he
  norm_num only [Nat.cast_ofNat] at he
  dsimp [baseLog,peakLog]
  nlinarith

theorem baseLog_hasDerivAt {q x : ℝ} (hx : 0 < x) :
    HasDerivAt (baseLog q) (-q*(2*x)+x⁻¹/3) x := by
  change HasDerivAt (fun y => -q*y^2+Real.log y/3) _ x
  convert (((hasDerivAt_id x).pow 2).const_mul (-q)).add
    ((Real.hasDerivAt_log hx.ne').div_const 3) using 1 <;>
    first | rfl | (funext y; rfl) | norm_num

theorem baseLog_antitone_after_peak {q a : ℝ}
    (hq : 0 < q) (ha : 0 < a) (hpeak : 1 ≤ 6*q*a^2) :
    AntitoneOn (baseLog q) (Ici a) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici a)
  · intro x hx
    exact (baseLog_hasDerivAt (ha.trans_le hx)).continuousAt.continuousWithinAt
  · intro x hx
    exact (baseLog_hasDerivAt (ha.trans_le (interior_subset hx))).differentiableAt.differentiableWithinAt
  · intro x hx
    have hax : a ≤ x := interior_subset hx
    have hxp : 0 < x := ha.trans_le hax
    rw [(baseLog_hasDerivAt hxp).deriv]
    have hs : a^2 ≤ x^2 := by nlinarith
    have hm : 1 ≤ 6*q*x^2 := hpeak.trans (mul_le_mul_of_nonneg_left hs (by positivity))
    have hinv : x*x⁻¹ = 1 := mul_inv_cancel₀ hxp.ne'
    have hn : x*(-q*(2*x)+x⁻¹/3) ≤ 0 := by nlinarith
    exact nonpos_of_mul_nonpos_right hn hxp

noncomputable def peakX : ℝ := Real.sqrt (1/(6*(601/2500:ℝ)))
noncomputable def universalPeak : ℝ := Real.exp (peakLog (601/2500))
noncomputable def sourceShapeWeight (h x : ℝ) : ℝ :=
  Real.exp (-(601/2500:ℝ)*x^2)*x^((1:ℝ)/3)*
    (1+max (Real.log x) 0/h)^2

theorem peakX_positive : 0 < peakX := by unfold peakX; positivity
theorem peakX_le_one : peakX ≤ 1 := by
  unfold peakX
  apply (Real.sqrt_le_iff).mpr
  norm_num
theorem peakX_equation : 6*(601/2500:ℝ)*peakX^2 = 1 := by
  rw [peakX, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 1/(6*(601/2500:ℝ)))]
  norm_num

theorem baseLog_peakX : baseLog (601/2500) peakX = peakLog (601/2500) := by
  have hq : (0:ℝ) < 1/(6*(601/2500:ℝ)) := by norm_num
  unfold baseLog peakX peakLog
  rw [Real.sq_sqrt hq.le,Real.log_sqrt hq.le,Real.log_div one_ne_zero (by norm_num)]
  simp only [Real.log_one]
  ring

theorem sourceShapeWeight_of_le_one {h x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    sourceShapeWeight h x = Real.exp (baseLog (601/2500) x) := by
  have hl : Real.log x ≤ 0 := Real.log_nonpos hx.le hx1
  rw [sourceShapeWeight,max_eq_right hl]
  simp only [zero_div,add_zero,one_pow,mul_one,baseLog]
  rw [Real.rpow_def_of_pos hx,← Real.exp_add]
  congr 1
  ring

theorem sourceShapeWeight_of_one_le {h x : ℝ} (hh : 14 ≤ h) (hx : 1 ≤ x) :
    sourceShapeWeight h x = Real.exp (tailLog h x) := by
  have hp : 0 < h := by linarith
  have xp : 0 < x := by linarith
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx
  have hs : 0 < h+Real.log x := by linarith
  have he : 1+Real.log x/h = (h+Real.log x)/h := by field_simp
  rw [sourceShapeWeight,max_eq_left hl,he,Real.rpow_def_of_pos xp]
  have hn : (h+Real.log x)/h = Real.exp (Real.log (h+Real.log x)-Real.log h) := by
    rw [Real.exp_sub,Real.exp_log hs,Real.exp_log hp]
  rw [hn,← Real.exp_nat_mul,← Real.exp_add,← Real.exp_add]
  congr 1
  unfold tailLog
  ring

theorem sourceShapeWeight_peakX (h : ℝ) : sourceShapeWeight h peakX = universalPeak := by
  rw [sourceShapeWeight_of_le_one peakX_positive peakX_le_one,baseLog_peakX,universalPeak]

theorem sourceShapeWeight_continuousOn {h : ℝ} :
    ContinuousOn (sourceShapeWeight h) (Ioi 0) := by
  unfold sourceShapeWeight
  apply ContinuousOn.mul
  · apply ContinuousOn.mul
    · fun_prop
    · apply ContinuousOn.rpow_const continuousOn_id
      intro x hx
      exact Or.inl (ne_of_gt hx)
  · apply ContinuousOn.pow
    apply ContinuousOn.add continuousOn_const
    apply ContinuousOn.div_const
    have hl : ContinuousOn Real.log (Ioi (0:ℝ)) :=
      Real.continuousOn_log.mono (fun x hx => ne_of_gt hx)
    exact continuous_max.comp_continuousOn (hl.prodMk continuousOn_const)

theorem sourceShapeWeight_hasDerivAt_low {h x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    HasDerivAt (sourceShapeWeight h)
      (Real.exp (baseLog (601/2500) x)*(-(601/2500:ℝ)*(2*x)+x⁻¹/3)) x := by
  have hd := (baseLog_hasDerivAt (q:=601/2500) hx).exp
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hx hx1] with y hy
  exact sourceShapeWeight_of_le_one hy.1 hy.2.le

theorem sourceShapeWeight_hasDerivAt_high {h x : ℝ} (hh : 14 ≤ h) (hx : 1 < x) :
    HasDerivAt (sourceShapeWeight h) (Real.exp (tailLog h x)*tailD h x) x := by
  have hd := (tailLog_hasDerivAt hh hx.le).exp
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hx] with y hy
  exact sourceShapeWeight_of_one_le hh hy.le

theorem sourceShapeWeight_antitone {h : ℝ} (hh : 14 ≤ h) :
    AntitoneOn (sourceShapeWeight h) (Ici peakX) := by
  have hb := baseLog_antitone_after_peak (by norm_num : (0:ℝ) < 601/2500)
    peakX_positive (le_of_eq peakX_equation.symm)
  intro x hx y hy hxy
  have xp : 0 < x := peakX_positive.trans_le hx
  have yp : 0 < y := xp.trans_le hxy
  by_cases hy1 : y ≤ 1
  · rw [sourceShapeWeight_of_le_one xp (hxy.trans hy1),sourceShapeWeight_of_le_one yp hy1]
    exact Real.exp_le_exp.mpr (hb hx hy hxy)
  · have hy1' : 1 ≤ y := le_of_not_ge hy1
    by_cases hx1 : 1 ≤ x
    · rw [sourceShapeWeight_of_one_le hh hx1,sourceShapeWeight_of_one_le hh hy1']
      exact exp_tailLog_antitone hh hx1 hy1' hxy
    · have hx1' : x ≤ 1 := le_of_not_ge hx1
      calc sourceShapeWeight h y ≤ sourceShapeWeight h 1 := by
             rw [sourceShapeWeight_of_one_le hh hy1',sourceShapeWeight_of_one_le hh le_rfl]
             exact exp_tailLog_antitone hh (by norm_num) hy1' hy1'
           _ ≤ sourceShapeWeight h x := by
             rw [sourceShapeWeight_of_le_one (by norm_num : (0:ℝ)<1) le_rfl,
               sourceShapeWeight_of_le_one xp hx1']
             exact Real.exp_le_exp.mpr (hb hx peakX_le_one hx1')

theorem sourceShapeWeight_le_peak {h x : ℝ} (hh : 14 ≤ h) (hx : 0 < x) :
    sourceShapeWeight h x ≤ universalPeak := by
  by_cases h1 : x ≤ 1
  · rw [sourceShapeWeight_of_le_one hx h1,universalPeak]
    exact Real.exp_le_exp.mpr (baseLog_le_peak (by norm_num) hx)
  · have h1' : 1 ≤ x := le_of_not_ge h1
    calc sourceShapeWeight h x ≤ sourceShapeWeight h 1 :=
           sourceShapeWeight_antitone hh peakX_le_one (peakX_le_one.trans h1') h1'
         _ ≤ universalPeak := by
           rw [sourceShapeWeight_of_le_one (by norm_num : (0:ℝ)<1) le_rfl,universalPeak]
           exact Real.exp_le_exp.mpr (baseLog_le_peak (by norm_num) (by norm_num))

#print axioms sourceShapeWeight_antitone
#print axioms sourceShapeWeight_le_peak
end SynergyAnalytic
