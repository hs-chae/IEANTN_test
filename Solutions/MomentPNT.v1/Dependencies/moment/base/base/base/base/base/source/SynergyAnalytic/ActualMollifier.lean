import WinnerBetaA.ActualObject
import SynergyAnalytic.FiniteMoment

namespace SynergyAnalytic
open Real Set MeasureTheory WinnerBetaA.ActualObject
set_option maxHeartbeats 0

/-- The actual source mollifier, not a freely supplied model function. -/
noncomputable def mollifierMass (T x : ℝ) : ℝ :=
  ∫ u in (0:ℝ)..(x*T), ‖mollifier T (vertical (1/2) u)‖^2
noncomputable def mollifierMassD (T x : ℝ) : ℝ :=
  T*‖mollifier T (vertical (1/2) (x*T))‖^2

theorem mollifierMass_hasDerivAt (T x : ℝ) :
    HasDerivAt (mollifierMass T) (mollifierMassD T x) x := by
  have hg : Continuous (fun u : ℝ => ‖mollifier T (vertical (1/2) u)‖^2) :=
    (((mollifier_continuous T).comp (vertical_continuous (1/2))).norm.pow 2)
  have hd := intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable 0 (x*T))
    hg.aestronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt
  have hc := hd.comp x ((hasDerivAt_id x).mul_const T)
  convert hc using 1 <;> first | rfl | simp [mollifierMass,mollifierMassD,mul_comm]

theorem mollifierMass_continuous (T : ℝ) : Continuous (mollifierMass T) :=
  continuous_iff_continuousAt.mpr (fun x => (mollifierMass_hasDerivAt T x).continuousAt)

theorem mollifierMassD_continuous (T : ℝ) : Continuous (mollifierMassD T) := by
  unfold mollifierMassD
  apply Continuous.const_mul
  apply Continuous.pow
  apply Continuous.norm
  exact ((mollifier_continuous T).comp (vertical_continuous (1/2))).comp
    (continuous_id.mul_const T)

/-- A direct application to the original mollifier mean-square hypothesis.
It replaces height-by-height Gaussian cell caps by one universal analytic shape;
the remaining area is an explicit Gaussian/log integral, not an assumed U bound. -/
theorem actual_mollifier_weighted_bound
    {T h b m1 m2 : ℝ} (hT : 0 < T) (hh : 14 ≤ h) (hb : 1 ≤ b)
    (hmean : ∀ t > 0,
      (∫ u in (0:ℝ)..t, ‖mollifier T (vertical (1/2) u)‖^2) ≤
        (m1*t+m2*T)*Real.log T) :
    (∫ x in (0:ℝ)..b, sourceShapeWeight h x*mollifierMassD T x) ≤
      (T*Real.log T)*(m1*(universalPeak*peakX+
        ∫ x in peakX..b, sourceShapeWeight h x)+m2*universalPeak) := by
  have hc : ∀ x ∈ Icc 0 b, mollifierMass T x ≤
      (T*Real.log T*m1)*x+(T*Real.log T*m2) := by
    intro x hx
    rcases eq_or_lt_of_le hx.1 with he | hp
    · subst x
      have hm := hmean (T) hT
      have hlim : 0 ≤ (T*Real.log T*m2) := by
        have hneg : ∀ n : ℕ, 0 ≤ (m1*(T/(n+1))+m2*T)*Real.log T := by
          intro n
          exact (intervalIntegral.integral_nonneg_of_forall
            (by positivity : (0:ℝ) ≤ T/(n+1)) (by intro u;positivity)).trans
            (hmean (T/(n+1)) (by positivity))
        have htend : Filter.Tendsto (fun n : ℕ => (m1*(T/(n+1))+m2*T)*Real.log T)
            Filter.atTop (nhds (m2*T*Real.log T)) := by
          have hz : Filter.Tendsto (fun n : ℕ => T/((n:ℝ)+1)) Filter.atTop (nhds 0) := by
            simpa only [mul_zero,mul_one_div] using
              (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).const_mul T
          simpa only [mul_zero,zero_add] using ((hz.const_mul m1).add_const (m2*T)).mul_const (Real.log T)
        have hl := ge_of_tendsto htend (Filter.Eventually.of_forall hneg)
        nlinarith
      simpa [mollifierMass] using hlim
    · have hr := hmean (x*T) (mul_pos hp hT)
      convert hr using 1 <;> first | rfl | ring
  have hh0 : mollifierMass T 0 = 0 := by simp [mollifierMass]
  have hf0 : ∀ x ∈ Icc 0 b, 0 ≤ mollifierMassD T x := by
    intro x hx
    unfold mollifierMassD
    positivity
  have hr := shape_weight_cdf_bound hh hb (mollifierMass_continuous T).continuousOn
    (mollifierMassD_continuous T).continuousOn
    (fun x hx => mollifierMass_hasDerivAt T x) hh0 hf0 hc
  convert hr using 1 <;> ring

#print axioms actual_mollifier_weighted_bound
end SynergyAnalytic
