/- Copyright (c) 2026 IEANTN contributors. Released under Apache2.0. -/
import Mathlib
namespace WinnerWarmPade
open Real
set_option maxHeartbeats 0

/-- A finite lower-Pade certificate for the original logarithmic count model.
The lower numerator and upper denominator operands are independently explicit. -/
theorem log_count_lower {rlo r rhi zl z : ℝ}
    (hrlo0 : 0 ≤ rlo) (hrlor : rlo ≤ r) (hr : 0<r) (hrrhi : r ≤ rhi)
    (hzl : 0 ≤ zl) (hzlz : zl ≤ z) :
    rlo*2*zl/(2*rhi+zl) ≤ r*log (1+z/r) := by
  have hz : 0 ≤ z := hzl.trans hzlz
  have hd : 0<2*r+zl := by positivity
  have hd' : 0<2*r+z := by positivity
  have hdh : 0<2*rhi+zl := by linarith
  have hfirst : 2*zl/(2*rhi+zl) ≤ 2*zl/(2*r+zl) := by
    apply div_le_div_of_nonneg_left (by positivity) hd
    linarith
  have hsecond : 2*zl/(2*r+zl) ≤ 2*z/(2*r+z) := by
    apply (div_le_div_iff₀ hd hd').mpr
    nlinarith
  have hratio:=hfirst.trans hsecond
  have hm:=mul_le_mul hrlor hratio (by positivity : 0 ≤ 2*zl/(2*rhi+zl)) hr.le
  have hlog:=mul_le_mul_of_nonneg_left
    (le_log_one_add_of_nonneg (div_nonneg hz hr.le)) hr.le
  have heq : r*(2*(z/r)/(z/r+2))=r*2*z/(2*r+z) := by
    field_simp
    <;> ring
  rw [heq] at hlog
  calc rlo*2*zl/(2*rhi+zl)=rlo*(2*zl/(2*rhi+zl)) := by ring
       _  ≤ r*(2*z/(2*r+z)) := hm
       _ =r*2*z/(2*r+z) := by ring
       _  ≤ r*log (1+z/r) := hlog

/-- Scale a positive lower profile by a single band maximum before taking the
total-count minimum. This applies to any exponential profile pointwise. -/
theorem warm_profile_lower {f fmax count G : ℝ}
    (hf : 0 ≤ f) (hffmax : f ≤ fmax) (hmax : 0<fmax)
    (hfc : f ≤ count) (hG : 0 ≤ G) :
    min fmax G/fmax*f  ≤  min count G := by
  have hmin : 0 ≤ min fmax G := le_min hmax.le hG
  have ha : 0 ≤ min fmax G/fmax := div_nonneg hmin hmax.le
  have ha1 : min fmax G/fmax ≤ 1 := (div_le_one hmax).mpr (min_le_left _ _)
  apply le_min
  · have hh:=mul_le_mul_of_nonneg_right ha1 hf
    simpa using hh.trans (by simpa using hfc)
  · have hh:=mul_le_mul_of_nonneg_left hffmax ha
    have heq : min fmax G/fmax*fmax=min fmax G := div_mul_cancel₀ _ hmax.ne'
    exact (hh.trans_eq heq).trans (min_le_right _ _)

#print axioms log_count_lower
#print axioms warm_profile_lower
end WinnerWarmPade
