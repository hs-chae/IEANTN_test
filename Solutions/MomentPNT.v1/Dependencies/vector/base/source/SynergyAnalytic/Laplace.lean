import Mathlib
namespace SynergyAnalytic
open Real Set MeasureTheory
set_option maxHeartbeats 0

/-- The paired zero-density boundary/integral contribution.  This representation
retains its full log-height profile, rather than freezing its endpoint value. -/
noncomputable def pairedFactor (D r L : ℝ) : ℝ :=
  1+D*(∫ u in (0:ℝ)..r, Real.exp ((D-L)*u))

theorem pairedFactor_antitone {D r : ℝ} (hD : 0 ≤ D) (hr : 0 ≤ r) :
    Antitone (pairedFactor D r) := by
  intro L K hLK
  unfold pairedFactor
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ hD
  apply intervalIntegral.integral_mono_on hr
    ((by fun_prop : Continuous (fun u : ℝ => Real.exp ((D-K)*u))).intervalIntegrable 0 r)
    ((by fun_prop : Continuous (fun u : ℝ => Real.exp ((D-L)*u))).intervalIntegrable 0 r)
  intro u hu
  apply Real.exp_le_exp.mpr
  nlinarith [hu.1]

theorem pairedFactor_ge_one {D r L : ℝ} (hD : 0 ≤ D) (hr : 0 ≤ r) :
    1 ≤ pairedFactor D r L := by
  have hn : 0 ≤ (∫ u in (0:ℝ)..r, Real.exp ((D-L)*u)) :=
    intervalIntegral.integral_nonneg_of_forall hr (by intro u;positivity)
  unfold pairedFactor
  nlinarith

theorem pairedFactor_closed {D r L : ℝ} (hne : L-D ≠ 0) :
    pairedFactor D r L = Real.exp (-(L-D)*r)+
      L*(1-Real.exp (-(L-D)*r))/(L-D) := by
  have hn : D-L ≠ 0 := sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp hne))
  have hd : ∀ u : ℝ, HasDerivAt
      (fun v : ℝ => Real.exp ((D-L)*v)/(D-L)) (Real.exp ((D-L)*u)) u := by
    intro u
    convert ((((hasDerivAt_id u).const_mul (D-L)).exp).div_const (D-L)) using 1 <;>
      first | rfl | (simp only [id_eq,mul_one];field_simp)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u hu => hd u)
    ((by fun_prop : Continuous (fun u : ℝ => Real.exp ((D-L)*u))).intervalIntegrable 0 r)
  simp only [mul_zero,Real.exp_zero] at hi
  unfold pairedFactor
  rw [hi]
  have he : D-L = -(L-D) := by ring
  rw [he]
  field_simp
  <;> ring

theorem pairedFactor_at_diagonal (D r : ℝ) : pairedFactor D r D = 1+D*r := by
  simp [pairedFactor]

/-- A pointwise comparison with only the old Gaussian moment cannot improve
the normalization at the unit-band endpoint.  This is an obstruction to one
proposed shortcut, not an obstruction to general analytic interpolation. -/
theorem endpoint_comparison_obstruction {alpha R k : ℝ}
    (hunit : 1 ≤ k) (hdom : k ≤ R*Real.exp (-2*alpha)) :
    Real.exp (2*alpha) ≤ R := by
  have hh : Real.exp (2*alpha)*Real.exp (-2*alpha) = 1 := by
    rw [← Real.exp_add]
    simp
  have hmul := mul_le_mul_of_nonneg_right (hunit.trans hdom) (Real.exp_pos (2*alpha)).le
  have hmul' : R*Real.exp (-2*alpha)*Real.exp (2*alpha) = R := by
    rw [mul_assoc,← Real.exp_add]
    simp
  rw [hmul'] at hmul
  simpa using hmul

#print axioms pairedFactor_antitone
#print axioms pairedFactor_closed
#print axioms endpoint_comparison_obstruction
end SynergyAnalytic
