import SynergyAnalytic.ActualMoment
import SynergyAnalytic.BasisTail
namespace SynergyAnalytic
open Real Set MeasureTheory
set_option maxHeartbeats 0

theorem finite_integral_from_tail
    {f g : ℝ → ℝ} {a c : ℝ} (hac : a ≤ c)
    (hf : ContinuousOn f (Ici a)) (hfp : ∀ x ≥ a, 0 ≤ f x)
    (hg : Continuous g) (hgi : IntegrableOn g (Ioi c))
    (hgp : ∀ x ≥ c, 0 ≤ g x) (hdom : ∀ x ≥ c, f x ≤ g x)
    {b : ℝ} (hb : a ≤ b) :
    (∫ x in a..b, f x) ≤ (∫ x in a..c, f x)+∫ x in Ioi c, g x := by
  have hfi : ∀ v w : ℝ, a ≤ v → v ≤ w → IntervalIntegrable f volume v w := by
    intro v w hv hvw
    apply ContinuousOn.intervalIntegrable
    exact hf.mono (by rw [uIcc_of_le hvw];intro x hx;exact hv.trans hx.1)
  have htailp : 0 ≤ ∫ x in Ioi c, g x :=
    setIntegral_nonneg measurableSet_Ioi (by intro x hx;exact hgp x hx.le)
  by_cases hbc : b ≤ c
  · have he := intervalIntegral.integral_add_adjacent_intervals (hfi a b le_rfl hb) (hfi b c hb hbc)
    have hn : 0 ≤ (∫ x in b..c, f x) := intervalIntegral.integral_nonneg hbc
      (by intro x hx;exact hfp x (hb.trans hx.1))
    linarith
  · have hcb : c ≤ b := le_of_not_ge hbc
    have hsplit := intervalIntegral.integral_add_adjacent_intervals (hfi a c le_rfl hac) (hfi c b hac hcb)
    have hm : (∫ x in c..b, f x) ≤ ∫ x in c..b, g x :=
      intervalIntegral.integral_mono_on hcb (hfi c b hac hcb) (hg.intervalIntegrable c b)
        (by intro x hx;exact hdom x hx.1)
    have hgb : IntegrableOn g (Ioi b) := hgi.mono_set (by intro x hx;exact hcb.trans_lt hx)
    have hgsplit := intervalIntegral.integral_interval_add_Ioi hgi hgb
    have hposb : 0 ≤ ∫ x in Ioi b, g x :=
      setIntegral_nonneg measurableSet_Ioi (by intro x hx;exact hgp x (hcb.trans hx.le))
    linarith

noncomputable def cubicTail (c : ℝ) : ℝ :=
  Real.exp (-(601/2500:ℝ)*c^2)*((601/2500:ℝ)*c^2+1)/(2*(601/2500:ℝ)^2)

theorem basis_finite_tail_bound {a c : ℝ} (ha : 0 < a) (hac : a ≤ c) (hc : 1 ≤ c)
    {k : ℕ} (hk : k ≤ 2) (hpos : ∀ x ≥ a, 0 ≤ baseWeight x*(Real.log x)^k)
    {b : ℝ} (hb : a ≤ b) :
    (∫ x in a..b, baseWeight x*(Real.log x)^k) ≤
      (∫ x in a..c, baseWeight x*(Real.log x)^k)+cubicTail c := by
  have hf : ContinuousOn (fun x => baseWeight x*(Real.log x)^k) (Ici a) := by
    intro x hx
    have xp : 0 < x := ha.trans_le hx
    exact baseWeight_continuous.continuousAt.continuousWithinAt.mul
      ((Real.continuousAt_log xp.ne').continuousWithinAt.pow k)
  have hg : Continuous (fun x : ℝ => x^3*Real.exp (-(601/2500:ℝ)*x^2)) := by fun_prop
  have hgi : IntegrableOn (fun x : ℝ => x^3*Real.exp (-(601/2500:ℝ)*x^2)) (Ioi c) := by
    simpa only [Real.rpow_ofNat] using
      (integrable_rpow_mul_exp_neg_mul_sq (by norm_num : (0:ℝ)<601/2500) (s:=3) (by norm_num)).integrableOn (s:=Ioi c)
  have hr := finite_integral_from_tail hac hf hpos hg hgi
    (by intro x hx;have xp : 0≤x := (by norm_num : (0:ℝ)≤1).trans (hc.trans hx);positivity)
    (by intro x hx;exact log_basis_le_cubic (hc.trans hx) hk) hb
  rw [gaussian_cubic_tail (by norm_num : (0:ℝ)<601/2500)] at hr
  exact hr

/-- The universal residual contract reduces to three finite integrals plus an
explicit common tail.  These are exactly the finite numerical obligations for
a source-linked producer; no numerical values are assumed by this theorem. -/
theorem basis_caps_of_three_finite
    {j0 j1 j2 : ℝ}
    (h0 : universalPeak*(5/6:ℝ)+(∫ x in (5/6:ℝ)..16, baseWeight x)+cubicTail 16 ≤ j0)
    (h1 : (∫ x in (1:ℝ)..16, baseWeight x*Real.log x)+cubicTail 16 ≤ j1)
    (h2 : (∫ x in (1:ℝ)..16, baseWeight x*(Real.log x)^2)+cubicTail 16 ≤ j2) :
    UniversalBasisCaps j0 j1 j2 := by
  intro b hb
  have hp0 : ∀ x ≥ (5/6:ℝ), 0 ≤ baseWeight x*(Real.log x)^0 := by
    intro x hx
    have xp : 0 ≤ x := by linarith
    unfold baseWeight
    positivity
  have hp : ∀ k : ℕ, ∀ x ≥ (1:ℝ), 0 ≤ baseWeight x*(Real.log x)^k := by
    intro k x hx
    have xp : 0 ≤ x := by linarith
    have hl : 0 ≤ Real.log x := Real.log_nonneg hx
    unfold baseWeight
    positivity
  have hb0 := basis_finite_tail_bound (by norm_num : (0:ℝ)<5/6) (by norm_num : (5/6:ℝ)≤16)
    (by norm_num : (1:ℝ)≤16) (by norm_num : (0:ℕ)≤2) hp0 (by linarith : (5/6:ℝ)≤b)
  simp only [pow_zero,mul_one] at hb0
  have hb1 := basis_finite_tail_bound (by norm_num : (0:ℝ)<1) (by norm_num : (1:ℝ)≤16)
    (by norm_num : (1:ℝ)≤16) (by norm_num : (1:ℕ)≤2) (hp 1) hb
  simp only [pow_one] at hb1
  have hb2 := basis_finite_tail_bound (by norm_num : (0:ℝ)<1) (by norm_num : (1:ℝ)≤16)
    (by norm_num : (1:ℝ)≤16) (by norm_num : (2:ℕ)≤2) (hp 2) hb
  have hz := basisZero_rational_prefix hb
  refine ⟨?_,?_,?_⟩
  · linarith
  · exact hb1.trans h1
  · exact hb2.trans h2

#print axioms basis_caps_of_three_finite
end SynergyAnalytic
