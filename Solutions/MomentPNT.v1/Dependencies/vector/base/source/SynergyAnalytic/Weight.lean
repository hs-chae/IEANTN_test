import Mathlib
namespace SynergyAnalytic
open Real Set
set_option maxHeartbeats 0
set_option maxRecDepth 20000
noncomputable def tailLog (h x : ℝ) : ℝ :=
  -(601/2500:ℝ)*x^2 + Real.log x/3 + 2*Real.log (h+Real.log x)-2*Real.log h
noncomputable def tailD (h x : ℝ) : ℝ :=
  (-(601/1250:ℝ)*x^2*(h+Real.log x)+(h+Real.log x)/3+2)/(x*(h+Real.log x))

theorem tailLog_hasDerivAt {h x : ℝ} (hh : 14 ≤ h) (hx : 1 ≤ x) :
    HasDerivAt (tailLog h) (tailD h x) x := by
  have xp : 0 < x := by linarith
  have lp : 0 ≤ Real.log x := Real.log_nonneg hx
  have hp : 0 < h+Real.log x := by linarith
  have hd := (((((hasDerivAt_id x).pow 2).const_mul (-(601/2500:ℝ))).add
    ((Real.hasDerivAt_log xp.ne').div_const 3)).add
    (((Real.hasDerivAt_log hp.ne').comp x
      ((hasDerivAt_const x h).add (Real.hasDerivAt_log xp.ne'))).const_mul 2)).sub_const
        (2*Real.log h)
  have he : tailD h x = -(601/2500:ℝ)*(2*x)+x⁻¹/3+2*((h+Real.log x)⁻¹*x⁻¹) := by
    unfold tailD
    field_simp [ne_of_gt xp,ne_of_gt hp]
    <;> ring
  rw [he]
  change HasDerivAt (fun y => -(601/2500:ℝ)*y^2 + Real.log y/3 +
    2*Real.log (h+Real.log y)-2*Real.log h) _ x
  simpa using hd

theorem tailD_nonpos {h x : ℝ} (hh : 14 ≤ h) (hx : 1 ≤ x) : tailD h x ≤ 0 := by
  have xp : 0 < x := by linarith
  have lp : 0 ≤ Real.log x := Real.log_nonneg hx
  have hp : 0 < h+Real.log x := by linarith
  have x2 : 1 ≤ x^2 := by nlinarith
  have prod : h+Real.log x ≤ x^2*(h+Real.log x) := by nlinarith
  unfold tailD
  apply (div_le_iff₀ (mul_pos xp hp)).mpr
  nlinarith

theorem tailLog_antitone {h : ℝ} (hh : 14 ≤ h) : AntitoneOn (tailLog h) (Ici 1) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici 1)
  · intro x hx
    exact (tailLog_hasDerivAt hh hx).continuousAt.continuousWithinAt
  · intro x hx
    exact (tailLog_hasDerivAt hh (interior_subset hx)).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [(tailLog_hasDerivAt hh (interior_subset hx)).deriv]
    exact tailD_nonpos hh (interior_subset hx)

theorem exp_tailLog_antitone {h : ℝ} (hh : 14 ≤ h) :
    AntitoneOn (fun x => Real.exp (tailLog h x)) (Ici 1) := by
  intro x hx y hy hxy
  exact Real.exp_le_exp.mpr (tailLog_antitone hh hx hy hxy)

/-- A polynomial-Gaussian window is at least one on its unit ordinate band.
This is a generic analytic kernel statement, not a new zeta/source premise. -/
theorem flat_window_lower {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    u*Real.log 2 ≤ Real.log (1+u) := by
  have hc : ConcaveOn ℝ (Ioi (0:ℝ)) Real.log := (strictConcaveOn_log_Ioi).concaveOn
  have h := hc.2 (by norm_num : (1:ℝ) ∈ Ioi (0:ℝ)) (by norm_num : (2:ℝ) ∈ Ioi (0:ℝ))
    (show 0 ≤ 1-u by linarith) hu (by ring : (1-u)+u=1)
  simp only [smul_eq_mul,Real.log_one,mul_zero,zero_add] at h
  convert h using 1 <;> congr 1 <;> ring

#print axioms tailLog_antitone
#print axioms exp_tailLog_antitone
#print axioms flat_window_lower
end SynergyAnalytic
