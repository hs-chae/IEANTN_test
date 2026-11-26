/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitMellinGammaCancellation
import ExplicitDomain

set_option autoImplicit false
noncomputable section
open Real Set MeasureTheory
namespace RH080Next.Explicit

def logarithmicWindowMass (nodes : List ℚ) (m : ℕ) (d L y : ℝ) : ℝ :=
  |affineSpectrum nodes m ((log y-L)/d)|/y

/-- The exact absolute spectral mass in Mellin coordinates, including the
actual finite change of variables and integrability. -/
theorem logarithmic_window_mass_integral (nodes : List ℚ) (m : ℕ)
    (hlen : 2 ≤ nodes.length) (hm : 0 < m) (d L : ℝ) (hd : 0 < d) :
    IntervalIntegrable (logarithmicWindowMass nodes m d L) volume
      (exp (L-radius nodes m*d)) (exp (L+radius nodes m*d)) ∧
    (∫ y in exp (L-radius nodes m*d)..exp (L+radius nodes m*d), logarithmicWindowMass nodes m d L y) =
      d*(∫ v : ℝ, |affineSpectrum nodes m v|) := by
  let R := radius nodes m
  have hR : 0 ≤ R := by dsimp [R,radius]; positivity
  have hAB : -R ≤ R := by linarith
  have hc : Continuous (fun v : ℝ => exp (L+d*v)) := by fun_prop
  have hder (v : ℝ) : HasDerivAt (fun w : ℝ => exp (L+d*w)) (d*exp (L+d*v)) v := by
    simpa only [id_eq,mul_one,mul_comm] using (((hasDerivAt_id v).const_mul d).const_add L).exp
  have hderOn : ∀ v ∈ Ioo (min (-R) R) (max (-R) R),
      HasDerivAt (fun w : ℝ => exp (L+d*w)) (d*exp (L+d*v)) v := fun v hv => hder v
  have hnonneg : ∀ v ∈ Ioo (min (-R) R) (max (-R) R), 0 ≤ d*exp (L+d*v) := by intros; positivity
  have hiff := intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonneg
    (g := logarithmicWindowMass nodes m d L) hc.continuousOn hderOn hnonneg
  have hchange := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (g := logarithmicWindowMass nodes m d L) hc.continuousOn hderOn hnonneg
  dsimp only [Function.comp_def] at hiff hchange
  have heq : (fun v : ℝ => logarithmicWindowMass nodes m d L (exp (L+d*v))*(d*exp (L+d*v))) =
      (fun v : ℝ => d*|affineSpectrum nodes m v|) := by
    funext v
    unfold logarithmicWindowMass
    rw [log_exp,show (L+d*v-L)/d = v by field_simp; ring]
    field_simp
  rw [heq] at hiff hchange
  have hi : IntervalIntegrable (fun v : ℝ => |affineSpectrum nodes m v|) volume (-R) R :=
    (continuous_affineSpectrum nodes m).abs.intervalIntegrable _ _
  have hitarget := hiff.mp (hi.const_mul d)
  have harg : L+d*(-R) = L-R*d := by ring
  have harg' : L+d*R = L+R*d := by ring
  rw [harg,harg'] at hitarget hchange
  refine ⟨hitarget,?_⟩
  rw [intervalIntegral.integral_const_mul] at hchange
  rw [←hchange]
  congr 1
  rw [intervalIntegral.integral_of_le hAB,←integral_Icc_eq_integral_Ioc]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro v hv
  have hw : affineSpectrum nodes m v = 0 := by
    by_contra h
    exact hv (affineSpectrum_support_subset nodes m hlen hm h)
  simp [hw]

/-- The actual trivial-zero integral is bounded with the true lower support
endpoint. Radius-dependent geometry is retained exactly. -/
theorem trivial_integral_bound (nodes : List ℚ) (m : ℕ)
    (hlen : 2 ≤ nodes.length) (hm : 0 < m) (d L : ℝ) (hd : 0 < d)
    (hpositive : radius nodes m*d < L) :
    IntervalIntegrable (trivialYIntegrand nodes m d L) volume
      (exp (L-radius nodes m*d)) (exp (L+radius nodes m*d)) ∧
    |∫ y in exp (L-radius nodes m*d)..exp (L+radius nodes m*d), trivialYIntegrand nodes m d L y| ≤
      d*nodalMassA0 nodes m/
        (sqrt (exp (L-radius nodes m*d))*((exp (L-radius nodes m*d))^2-1)) := by
  let a := exp (L-radius nodes m*d)
  let b := exp (L+radius nodes m*d)
  let C := 1/(sqrt a*(a^2-1))
  have hR : 0 ≤ radius nodes m := by unfold radius; positivity
  have hab : a ≤ b := exp_le_exp.mpr (by nlinarith)
  have ha : 1 < a := one_lt_exp_iff.mpr (by linarith)
  have ha0 : 0 < a := lt_trans zero_lt_one ha
  have haSq : 0 < a^2-1 := by nlinarith
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have htcont : ContinuousOn (trivialYIntegrand nodes m d L) (uIcc a b) := by
    intro y hy
    rw [uIcc_of_le hab] at hy
    have hy1 : 1 < y := ha.trans_le hy.1
    have hy0 : y ≠ 0 := by linarith
    have hs : sqrt y ≠ 0 := (sqrt_pos.mpr (by linarith)).ne'
    have hsq : y^2-1 ≠ 0 := by nlinarith
    have hden : y*(y^2-1) ≠ 0 := mul_ne_zero hy0 hsq
    unfold trivialYIntegrand mellinArithmeticWeight
    have harg : ContinuousAt (fun y : ℝ => (log y-L)/d) y :=
      ((Real.continuousAt_log hy0).sub_const L).div_const d
    have hnum := (continuous_affineSpectrum nodes m).continuousAt.comp harg
    have hden' : ContinuousAt (fun y : ℝ => y*(y^2-1)) y := by fun_prop
    exact ((hnum.div Real.continuous_sqrt.continuousAt hs).div hden' hden).continuousWithinAt
  have hti := htcont.intervalIntegrable (μ := volume)
  obtain ⟨hmi,hmass⟩ := logarithmic_window_mass_integral nodes m hlen hm d L hd
  have hmib : IntervalIntegrable (logarithmicWindowMass nodes m d L) volume a b := hmi
  have hpoint : ∀ y ∈ Icc a b,
      |trivialYIntegrand nodes m d L y| ≤ C*logarithmicWindowMass nodes m d L y := by
    intro y hy
    have hy1 : 1 < y := ha.trans_le hy.1
    have hy0 : 0 < y := by linarith
    have hs : 0 < sqrt y := sqrt_pos.mpr hy0
    have hsq : 0 < y^2-1 := by nlinarith
    have has : 0 < sqrt a := sqrt_pos.mpr ha0
    have hasq : 0 < a^2-1 := by nlinarith
    have hay : a ≤ y := hy.1
    have hden : sqrt a*(a^2-1) ≤ sqrt y*(y^2-1) :=
      mul_le_mul (sqrt_le_sqrt hy.1) (by nlinarith) hasq.le hs.le
    have hi : 1/(sqrt y*(y^2-1)) ≤ C := by
      dsimp [C]
      exact one_div_le_one_div_of_le (mul_pos has hasq) hden
    have heq : |trivialYIntegrand nodes m d L y| =
        logarithmicWindowMass nodes m d L y*(1/(sqrt y*(y^2-1))) := by
      unfold trivialYIntegrand mellinArithmeticWeight logarithmicWindowMass
      rw [abs_div,abs_div,abs_mul,abs_of_pos hs,abs_of_pos hy0,abs_of_pos hsq]
      field_simp
      <;> ring
    rw [heq]
    have hn : 0 ≤ logarithmicWindowMass nodes m d L y := by unfold logarithmicWindowMass; positivity
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hi hn
  have hbound := intervalIntegral.integral_mono_on hab hti.abs (hmib.const_mul C) hpoint
  have habs := intervalIntegral.abs_integral_le_integral_abs (μ := volume) (f := trivialYIntegrand nodes m d L) hab
  rw [intervalIntegral.integral_const_mul,hmass] at hbound
  have hmassle := mul_le_mul_of_nonneg_left (integral_abs_affineSpectrum_le nodes m hlen hm) hd.le
  have hmul := mul_le_mul_of_nonneg_left hmassle hC
  refine ⟨hti,?_⟩
  dsimp [C] at hmul hbound
  change |∫ y in a..b, trivialYIntegrand nodes m d L y| ≤ d*nodalMassA0 nodes m/(sqrt a*(a^2-1))
  calc
    _ ≤ ∫ y in a..b, |trivialYIntegrand nodes m d L y| := habs
    _ ≤ (1/(sqrt a*(a^2-1)))*(d*(∫ v : ℝ, |affineSpectrum nodes m v|)) := hbound
    _ ≤ (1/(sqrt a*(a^2-1)))*(d*nodalMassA0 nodes m) := hmul
    _ = _ := by ring

/-- The actual trivial integral is smaller than the reserved 10^-8 over the
entire t-domain. A very coarse proved lower endpoint a>4 already suffices;
no table of large exponential values is needed. -/
theorem trivial_integral_bound_domain (nodes : List ℚ) (m : ℕ)
    (hlen : 2 ≤ nodes.length) (hm : 0 < m)
    (hR : radius nodes m ≤ 10) (hA : nodalMassA0 nodes m ≤ 2)
    (c t : ℝ) (hc : (1/2:ℝ) ≤ c) (hc1 : c ≤ 1) (ht : 42 ≤ t) :
    IntervalIntegrable (trivialYIntegrand nodes m (halfLogWidth c t) (t+halfLogWidth c t)) volume
      (exp ((t+halfLogWidth c t)-radius nodes m*halfLogWidth c t))
      (exp ((t+halfLogWidth c t)+radius nodes m*halfLogWidth c t)) ∧
    |∫ y in exp ((t+halfLogWidth c t)-radius nodes m*halfLogWidth c t)..
        exp ((t+halfLogWidth c t)+radius nodes m*halfLogWidth c t),
      trivialYIntegrand nodes m (halfLogWidth c t) (t+halfLogWidth c t) y| < (1/100000000:ℝ) := by
  let d := halfLogWidth c t
  let a := exp ((t+d)-radius nodes m*d)
  have hd := halfLogWidth_bounds c t hc hc1 ht
  have hpos := mellin_positive_frequency_domain c t (radius nodes m) hc hc1 ht hR
  obtain ⟨hi,hbound⟩ := trivial_integral_bound nodes m hlen hm d (t+d) hd.1 hpos
  have hgeom := support_lower_geometry c t (radius nodes m) hc hc1 ht hR
  have heq : t+(1-radius nodes m)*d = (t+d)-radius nodes m*d := by ring
  change exp t/2 < exp (t+(1-radius nodes m)*d) at hgeom
  rw [heq] at hgeom
  have ha : 4 < a := by
    have he := Real.add_one_le_exp t
    dsimp [a]
    linarith
  have hsqrt : 2 ≤ sqrt a := by
    have hh := sqrt_le_sqrt ha.le
    norm_num at hh
    exact hh
  have hsq : 15 ≤ a^2-1 := by nlinarith
  have hden : 30 ≤ sqrt a*(a^2-1) := by nlinarith
  have hA0 : 0 ≤ nodalMassA0 nodes m := by unfold nodalMassA0; positivity
  have hn : d*nodalMassA0 nodes m < (1/25000000:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hA hd.1.le
    dsimp [d]
    nlinarith
  have hfrac : d*nodalMassA0 nodes m/(sqrt a*(a^2-1)) < (1/100000000:ℝ) := by
    apply (div_lt_iff₀ (by linarith : 0 < sqrt a*(a^2-1))).mpr
    nlinarith
  exact ⟨hi,hbound.trans_lt hfrac⟩

#print axioms trivial_integral_bound_domain
#print axioms logarithmic_window_mass_integral
#print axioms trivial_integral_bound
end RH080Next.Explicit
