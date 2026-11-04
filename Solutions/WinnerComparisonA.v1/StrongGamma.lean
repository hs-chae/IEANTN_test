/- Copyright (c) 2026 IEANTN contributors. Released under Apache2.0. -/
import OriginalSharpScalars
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
namespace WinnerStrongC4
open Real WinnerOriginalScalars LeanCert.Core
set_option maxHeartbeats 0
set_option maxRecDepth 100000
/-- Exact rational finite harmonic sum comparison, independent of the PNT program. -/
theorem harmonic_2500_lower : (8401461/1000000:ℚ)≤harmonic 2500 := by native_decide
/-- One closed log enclosure; not a floating-point assumption. -/
theorem log_2501_upper : log (2501:ℝ)≤7824446/1000000 := by
  have hh:=closed_upper (.log (.const 2501)) (7824446/1000000) (by native_decide)
  simpa using hh

theorem gamma_lower : (577/1000:ℝ)≤eulerMascheroniConstant := by
  have hh : (8401461/1000000:ℝ)≤(harmonic 2500:ℝ) := by
    have hh:=Rat.cast_le (K:=ℝ) |>.mpr harmonic_2500_lower
    norm_num only [Rat.cast_div,Rat.cast_ofNat] at hh
    exact hh
  have hg:=eulerMascheroniSeq_lt_eulerMascheroniConstant 2500
  have hl:=log_2501_upper
  norm_num only [eulerMascheroniSeq,Nat.cast_ofNat] at hg
  linarith

#print axioms gamma_lower
end WinnerStrongC4
