import BoxFactorization
import BoxMellinCoefficients
import BoxIntegrability

/-! Actual evaluation of the first regularized Box moment, with no moment premise. -/
namespace RHOcticPush.BoxGamma
open Real Set Filter
open scoped Topology
set_option maxHeartbeats 0

lemma zetaSeries_finite_part :
    Tendsto (fun s : ℝ => zetaSeries s-1/s) (𝓝[>] 0) (𝓝 Real.eulerMascheroniConstant) := by
  have hs : Tendsto (fun s : ℝ => 1+s) (𝓝[>] 0) (𝓝[>] 1) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · convert! ((continuous_const.add continuous_id : Continuous (fun s : ℝ => 1+s)).tendsto 0).mono_left
        (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ) ≤ 𝓝 0) using 1 <;> norm_num
    · filter_upwards [self_mem_nhdsWithin] with s hs
      change 1<1+s
      change 0<s at hs
      linarith
  have hz := ZetaAsymptotics.tendsto_riemannZeta_sub_one_div_nhds_right.comp hs
  have hr := Complex.continuous_re.tendsto (Real.eulerMascheroniConstant:ℂ) |>.comp hz
  simp only [Complex.ofReal_re] at hr
  apply hr.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  change 0<s at hs
  dsimp only [Function.comp_apply]
  rw [←zetaSeries_eq hs]
  have hc : ((1+s:ℝ):ℂ)-1=(s:ℂ) := by push_cast;ring
  rw [hc]
  simp only [Complex.sub_re,Complex.div_ofReal_re,Complex.ofReal_re,Complex.one_re]

/-- Actual finite part; all functions are independently defined. -/
theorem actual_box_finite_part :
    Tendsto (fun s : ℝ => BoxMellin.mellin s-1/s) (𝓝[>] 0) (𝓝 (Real.log 2)) := by
  have hP := prefactor_hasDerivAt.continuousAt.tendsto.mono_left
    (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ) ≤ 𝓝 0)
  have hH := hSeries_continuousAt_zero.tendsto.mono_left
    (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ) ≤ 𝓝 0)
  have hSlope : Tendsto (fun s : ℝ => (prefactor s-1)/s) (𝓝[>] 0)
      (𝓝 (1-Real.eulerMascheroniConstant-Real.log 2)) := by
    simpa [smul_eq_mul,div_eq_mul_inv,mul_comm,prefactor_zero] using
      prefactor_hasDerivAt.tendsto_slope_zero_right
  have h := (hP.mul (zetaSeries_finite_part.add hH)).add hSlope
  rw [prefactor_zero,hSeries_zero] at h
  have he : 1*(Real.eulerMascheroniConstant+(2*log 2-1))+
      (1-Real.eulerMascheroniConstant-log 2)=log 2 := by ring
  rw [he] at h
  apply h.congr'
  filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ)<1 by norm_num)] with s hs
  rw [actual_box_factorization hs.1 hs.2]
  field_simp
  ring

/-- The original actual J0 identity, unconditionally derived from Mathlib. -/
theorem actual_box_J0 : IEANTN.RHSmoothing.J IEANTN.RHSmoothing.box 0 = Real.log 2 :=
  tendsto_nhds_unique BoxMellin.finite_part_tendsto actual_box_finite_part

/-- Complete canonical first-moment predicate, including genuine integrability. -/
theorem first_moment : BoxMellinInputs.v1.first_moment :=
  Box.first_moment_iff.mpr actual_box_J0

#print axioms zetaSeries_finite_part
#print axioms actual_box_J0
#print axioms first_moment
end RHOcticPush.BoxGamma
