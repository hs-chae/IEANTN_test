/- Copyright (c) 2026 IEANTN contributors. Released under Apache2.0. -/
import SourceDensityPoly
import LeanCert.Validity.Integration
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
namespace WinnerOldAnalytic
open Real Set MeasureTheory
set_option maxHeartbeats 0

/-- A global polynomial lower bound, used only to lower-enclose the old expression. -/
theorem log_one_add_lower {x : ℝ} (hx : 0 ≤ x) : x-x^2/2 ≤ log (1+x) := by
  have h := Real.le_log_one_add_of_nonneg hx
  have hp : 0 < x+2 := by linarith
  have hr : x-x^2/2 ≤ 2*x/(x+2) := by
    apply (le_div_iff₀ hp).mpr
    have hc := mul_nonneg hx (sq_nonneg x)
    nlinarith
  exact hr.trans h

theorem perspective_log_lower {r z : ℝ} (hr : 0 < r) (hz : 0 ≤ z) :
    z-z^2/(2*r) ≤ r*log (1+z/r) := by
  have h := mul_le_mul_of_nonneg_left (log_one_add_lower (div_nonneg hz hr.le)) hr.le
  have he : r*(z/r-(z/r)^2/2)=z-z^2/(2*r) := by field_simp
  rwa [he] at h

/-- This version multiplies the negative correction by the upper endpoint,
so it needs no unproved positivity of a lower Taylor polynomial. -/
theorem count_cell_lower {u ul ur r rmin z zl zu : ℝ}
    (hul : 0 ≤ ul) (hlu : ul ≤ u) (hur : u ≤ ur)
    (hr : 0 < rmin) (hrr : rmin ≤ r)
    (hzl : 0 ≤ zl) (hlz : zl ≤ z) (hzu : z ≤ zu) :
    ul*zl-ur*zu^2/(2*rmin) ≤ u*(r*log (1+z/r)) := by
  have hrp : 0 < r := hr.trans_le hrr
  have hzp : 0 ≤ z := hzl.trans hlz
  have hup : 0 ≤ u := hul.trans hlu
  have hurp : 0 ≤ ur := hup.trans hur
  have h1 := perspective_log_lower hrp hzp
  have hsq : z^2 ≤ zu^2 := pow_le_pow_left₀ hzp hzu 2
  have hdiv : z^2/(2*r) ≤ zu^2/(2*rmin) := by
    exact div_le_div₀ (sq_nonneg _) hsq (by positivity) (by linarith)
  have hmain : ul*zl ≤ u*z := mul_le_mul hlu hlz hzl hup
  have hcorr : u*(z^2/(2*r)) ≤ ur*(zu^2/(2*rmin)) :=
    mul_le_mul hur hdiv (by positivity) hurp
  have hm := mul_le_mul_of_nonneg_left h1 hup
  calc
    ul*zl-ur*zu^2/(2*rmin) = ul*zl-ur*(zu^2/(2*rmin)) := by ring
    _ ≤ u*z-u*(z^2/(2*r)) := sub_le_sub hmain hcorr
    _ = u*(z-z^2/(2*r)) := by ring
    _ ≤ _ := hm

noncomputable def expMass (k width : ℝ) : ℝ := (1-exp (-k*width))/k

theorem exp_mass_identity {k beta width : ℝ} (hk : k ≠ 0) :
    (∫ s in (beta-width)..beta, exp (k*(s-beta))) = expMass k width := by
  have hd : ∀ s : ℝ, HasDerivAt (fun t : ℝ => exp (k*(t-beta))/k)
      (exp (k*(s-beta))) s := by
    intro s
    convert! (((hasDerivAt_id s).sub_const beta).const_mul k).exp.div_const k using 1
    all_goals simp only [id_eq,mul_one]
    all_goals field_simp [hk]
  have hc : Continuous (fun s : ℝ => exp (k*(s-beta))) := by fun_prop
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s)
    (hc.intervalIntegrable (beta-width) beta)
  rw [hh]
  unfold expMass
  simp only [sub_self,mul_zero,exp_zero]
  congr 1
  ring

/-- Exact integration in sigma removes a second numerical quadrature. -/
theorem weighted_exponential_mass {A B K beta width : ℝ} (hK : K-B ≠ 0) :
    (∫ s in (beta-width)..beta, exp (K*(s-beta))*exp (A-B*s)) =
      exp (A-B*beta)*expMass (K-B) width := by
  have he : (fun s : ℝ => exp (K*(s-beta))*exp (A-B*s)) =
      fun s => exp (A-B*beta)*exp ((K-B)*(s-beta)) := by
    funext s
    rw [←exp_add,←exp_add]
    congr 1
    ring
  rw [he,intervalIntegral.integral_const_mul,exp_mass_identity hK]

theorem weighted_centered_mass {B K beta width : ℝ} (hK : K-B ≠ 0) :
    (∫ s in (beta-width)..beta, exp (K*(s-beta))*exp (B*(beta-s))) =
      expMass (K-B) width := by
  have he : (fun s : ℝ => exp (K*(s-beta))*exp (B*(beta-s))) =
      fun s => exp ((K-B)*(s-beta)) := by
    funext s
    rw [←exp_add]
    congr 1
    ring
  rw [he,exp_mass_identity hK]

theorem weighted_polynomial_mass {K beta width ul ur zl zu Bl Bu rmin den : ℝ}
    (hBl : K-Bl ≠ 0) (hBu : K-2*Bu ≠ 0) :
    (∫ s in (beta-width)..beta,
      exp (K*(s-beta))*(ul*(zl*exp (Bl*(beta-s)))-
        ur*(zu*exp (Bu*(beta-s)))^2/(2*rmin))/den) =
      (ul*zl*expMass (K-Bl) width-
        ur*zu^2/(2*rmin)*expMass (K-2*Bu) width)/den := by
  have he : (fun s : ℝ =>
      exp (K*(s-beta))*(ul*(zl*exp (Bl*(beta-s)))-
        ur*(zu*exp (Bu*(beta-s)))^2/(2*rmin))/den) =
      fun s => (ul*zl/den)*(exp (K*(s-beta))*exp (Bl*(beta-s)))-
        (ur*zu^2/(2*rmin)/den)*(exp (K*(s-beta))*exp ((2*Bu)*(beta-s))) := by
    funext s
    have hx : exp (Bu*(beta-s))^2=exp ((2*Bu)*(beta-s)) := by
      rw [pow_two,←exp_add]
      congr 1
      ring
    rw [mul_pow,hx]
    ring
  rw [he]
  have hc1 : Continuous (fun s : ℝ => exp (K*(s-beta))*exp (Bl*(beta-s))) := by fun_prop
  have hc2 : Continuous (fun s : ℝ => exp (K*(s-beta))*exp ((2*Bu)*(beta-s))) := by fun_prop
  rw [intervalIntegral.integral_sub ((hc1.const_mul _).intervalIntegrable _ _)
    ((hc2.const_mul _).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    weighted_centered_mass hBl,weighted_centered_mass hBu]
  ring

noncomputable def kernel (alpha den ratio y : ℝ) : ℝ :=
  exp (2*y-2*alpha*exp (2*y))*exp (y/3)*(1+y/den)^2*(exp y+ratio)
noncomputable def kernelCell (alpha den ratio l r : ℝ) : ℝ :=
  exp (2*l-2*alpha*exp (2*r))*exp (l/3)*(1+l/den)^2*(exp l+ratio)

theorem kernel_nonneg {alpha den ratio y : ℝ} (hr : 0 ≤ ratio) :
    0 ≤ kernel alpha den ratio y := by unfold kernel;positivity

theorem kernel_continuous (alpha den ratio : ℝ) : Continuous (kernel alpha den ratio) := by
  unfold kernel
  fun_prop

theorem kernel_cell_lower {alpha den ratio l r y : ℝ}
    (ha : 0 ≤ alpha) (hd : 0 < den) (hr : 0 ≤ ratio)
    (hfac : 0 ≤ 1+l/den) (hl : l ≤ y) (hy : y ≤ r) :
    kernelCell alpha den ratio l r ≤ kernel alpha den ratio y := by
  have he : exp l ≤ exp y := exp_le_exp.mpr hl
  have he3 : exp (l/3) ≤ exp (y/3) := exp_le_exp.mpr (by linarith)
  have hf : 1+l/den ≤ 1+y/den := by gcongr
  have hfy : 0 ≤ 1+y/den := hfac.trans hf
  have hw : exp (2*l-2*alpha*exp (2*r)) ≤ exp (2*y-2*alpha*exp (2*y)) := by
    apply exp_le_exp.mpr
    have hh : exp (2*y) ≤ exp (2*r) := exp_le_exp.mpr (by linarith)
    have hm := mul_le_mul_of_nonneg_left hh ha
    linarith
  unfold kernelCell kernel
  gcongr

/-- The finite lower sum is mathematically connected to the integral. -/
theorem kernel_grid_lower {alpha den ratio a step : ℝ} {n : ℕ}
    (ha : 0 ≤ alpha) (hd : 0 < den) (hr : 0 ≤ ratio)
    (hs : 0 ≤ step) (hfac : 0 ≤ 1+a/den) :
    (∑ k ∈ Finset.range n, step*kernelCell alpha den ratio
      (a+step*k) (a+step*k+step)) ≤
      ∫ y in a..(a+step*n), kernel alpha den ratio y := by
  let edge : ℕ → ℝ := fun k => a+step*k
  have hc := kernel_continuous alpha den ratio
  have hb : ∀ k ∈ Finset.range n,
      step*kernelCell alpha den ratio (edge k) (edge (k+1)) ≤
        (∫ y in edge k..edge (k+1), kernel alpha den ratio y) := by
    intro k hk
    have hed : edge k ≤ edge (k+1) := by dsimp [edge];push_cast;nlinarith
    have hfac' : 0 ≤ 1+edge k/den := by
      have hn : 0 ≤ step*(k:ℝ) := by positivity
      dsimp [edge]
      have hdiv : a/den ≤ (a+step*k)/den := by
        apply div_le_div_of_nonneg_right (by linarith) hd.le
      linarith
    have hh := intervalIntegral.integral_mono_on hed
      (intervalIntegrable_const : IntervalIntegrable
        (fun _ : ℝ => kernelCell alpha den ratio (edge k) (edge (k+1))) volume _ _)
      (hc.intervalIntegrable _ _)
      (fun y hy => kernel_cell_lower ha hd hr hfac' hy.1 hy.2)
    rw [intervalIntegral.integral_const] at hh
    have he : edge (k+1)-edge k=step := by dsimp [edge];push_cast;ring
    simpa [he,smul_eq_mul,mul_comm] using hh
  have hh := Finset.sum_le_sum hb
  rw [intervalIntegral.sum_integral_adjacent_intervals
    (fun k _ => hc.intervalIntegrable (edge k) (edge (k+1)))] at hh
  simpa only [edge,Nat.cast_zero,mul_zero,add_zero,Nat.cast_add,Nat.cast_one,
    mul_add,mul_one,add_assoc] using hh

#print axioms log_one_add_lower
#print axioms count_cell_lower
#print axioms weighted_exponential_mass
#print axioms weighted_polynomial_mass
#print axioms kernel_grid_lower
end WinnerOldAnalytic
