/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import SourceDensity
open Real
namespace WinnerDensitySource
/-- Exact k=1 shifted interpolation exponent, before the original loose relaxations. -/
theorem shifted_exponent_identity {sigma d delta L : ℝ} (hL : 0 < L) (hd : 0 ≤ delta) :
    ((1+delta/L)-(sigma-d/L))/((1+delta/L)-1/2) =
      2*(1-sigma)+(2*d+2*delta*(2*sigma-1))/(L+2*delta) := by
  have hDen : L+2*delta ≠ 0 := by positivity
  have hDen2 : (1+delta/L)-(1/2:ℝ) ≠ 0 := by
    have := div_nonneg hd hL.le
    linarith
  field_simp [hL.ne', hDen, hDen2]
  <;> ring_nf
  all_goals field_simp [hDen]
  all_goals ring


/-- Endpoint-only continuation for the exact centered interpolation exponent.
It follows from the tangent upper bound for log, without assuming differentiability of any min. -/
theorem centered_fraction_bound {P K q r h L : ℝ}
    (hP : 0 ≤ P) (hq : 0 ≤ q) (hr : 0 < r) (hh : 0 < h) (hL : h ≤ L)
    (hSlope : P*(1+q/h-Real.log (h*r))+K*q ≤ 0) :
    (P*Real.log (L*r)+K*L)/(L+q) ≤ (P*Real.log (h*r)+K*h)/(h+q) := by
  have hLp : 0 < L := hh.trans_le hL
  have hlogratio := Real.log_le_sub_one_of_pos (div_pos hLp hh)
  rw [Real.log_div hLp.ne' hh.ne'] at hlogratio
  have hdiv : (L-h)/h = L/h-1 := by field_simp
  have hlog : Real.log (L*r) ≤ Real.log (h*r)+(L-h)/h := by
    rw [Real.log_mul hLp.ne' hr.ne', Real.log_mul hh.ne' hr.ne']
    rw [hdiv]
    linarith
  have hleft : P*Real.log (L*r)+K*L ≤ P*(Real.log (h*r)+(L-h)/h)+K*L := by
    have hm := mul_le_mul_of_nonneg_left hlog hP
    linarith
  have hmiddle : (P*(Real.log (h*r)+(L-h)/h)+K*L)/(L+q) ≤
      (P*Real.log (h*r)+K*h)/(h+q) := by
    apply (div_le_div_iff₀ (by positivity : 0 < L+q) (by positivity : 0 < h+q)).mpr
    have hp := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hL) hSlope
    have heq : (P*(Real.log (h*r)+(L-h)/h)+K*L)*(h+q)-
        (P*Real.log (h*r)+K*h)*(L+q) =
          (L-h)*(P*(1+q/h-Real.log (h*r))+K*q) := by
      field_simp [hh.ne']
      <;> ring
    have hdiff : (P*(Real.log (h*r)+(L-h)/h)+K*L)*(h+q)-
        (P*Real.log (h*r)+K*h)*(L+q) ≤ 0 := by rw [heq]; exact hp
    linarith
  exact (div_le_div_of_nonneg_right hleft (by positivity)).trans hmiddle

/-- Global elementary upper bound for the centered log ratio. -/
theorem log_shift_ratio_upper {L q C : ℝ} (hL : 0 < L) (hq : 0 ≤ q) :
    (Real.log L+C)/(L+q) ≤ Real.exp (C-1) := by
  have ht := Real.add_one_le_exp (Real.log L+C-1)
  have he : Real.exp (Real.log L+C-1) = L*Real.exp (C-1) := by
    rw [show Real.log L+C-1 = Real.log L+(C-1) by ring, Real.exp_add, Real.exp_log hL]
  rw [he] at ht
  apply (div_le_iff₀ (by positivity : 0 < L+q)).mpr
  have hp := mul_nonneg hq (Real.exp_pos (C-1)).le
  nlinarith

/-- Exact interpolation budget, retaining V's negative correction and both log powers. -/
theorem uniform_interpolation_exponent_budget {sigma d delta L U V : ℝ}
    (hL : 0 < L) (hdelta : 0 ≤ delta) (hU : 0 < U) (hV : 0 < V)
    (hP : 0 ≤ 2*d+2*delta*(2*sigma-1)) :
    let P := 2*d+2*delta*(2*sigma-1)
    let a := 2*(1-sigma)+P/(L+2*delta)
    a*(Real.log U+3*Real.log L+4*L/3)+
        (1-a)*(Real.log V+2*Real.log L) ≤
      2*(1-sigma)*Real.log U+(2*sigma-1)*Real.log V+
        (4-2*sigma)*Real.log L+(8*(1-sigma)/3)*L+
          P*(4/3+(U/V)*Real.exp (-8*delta/3-1)) := by
  dsimp only
  let C := Real.log (U/V)-8*delta/3
  have hc := log_shift_ratio_upper (C := C) hL (by positivity : 0 ≤ 2*delta)
  have he : Real.exp (C-1) = (U/V)*Real.exp (-8*delta/3-1) := by
    dsimp [C]
    rw [show Real.log (U/V)-8*delta/3-1 = Real.log (U/V)+(-8*delta/3-1) by ring,
      Real.exp_add, Real.exp_log (div_pos hU hV)]
  rw [he] at hc
  have hm := mul_le_mul_of_nonneg_left hc hP
  have hDen : L+2*delta ≠ 0 := by positivity
  have halg :
      (2*(1-sigma)+(2*d+2*delta*(2*sigma-1))/(L+2*delta))*
          (Real.log U+3*Real.log L+4*L/3)+
        (1-(2*(1-sigma)+(2*d+2*delta*(2*sigma-1))/(L+2*delta)))*
          (Real.log V+2*Real.log L) =
      2*(1-sigma)*Real.log U+(2*sigma-1)*Real.log V+
        (4-2*sigma)*Real.log L+(8*(1-sigma)/3)*L+
          (2*d+2*delta*(2*sigma-1))*(4/3+(Real.log L+C)/(L+2*delta)) := by
    dsimp [C]
    rw [Real.log_div hU.ne' hV.ne']
    field_simp [hDen]
    <;> ring
  rw [halg]
  linarith

#print axioms log_shift_ratio_upper
#print axioms uniform_interpolation_exponent_budget
#print axioms centered_fraction_bound
#print axioms shifted_exponent_identity
end WinnerDensitySource
