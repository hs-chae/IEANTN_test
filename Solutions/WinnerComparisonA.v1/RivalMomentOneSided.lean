/- Copyright (c) 2026 IEANTN contributors. Released under Apache2.0. -/
import RivalMomentMath
namespace WinnerRivalMoments
open LeanCert.Core LeanCert.Engine MeasureTheory
set_option maxHeartbeats 0

theorem integral_lower_from_check (pos : Bool) (b step lo : ℚ) (degree count : ℕ)
    (hb : 0≤b) (hstep : 0≤step) (hcount : 0<count) (cfg : DyadicConfig)
    (hprec : cfg.precision≤0)
    (hlo : CH2QRH.DensityComputation.checkUpperBound
      (Expr.neg (cellExpr false pos b step degree)) 0 (count-1) (-lo) cfg=true) :
    (lo:ℝ)≤(∫y in (0:ℝ)..((step:ℝ)*count),moment pos b degree y) := by
  have hbl : (0:ℝ)≤b := by exact_mod_cast hb
  have hsl : (0:ℝ)≤step := by exact_mod_cast hstep
  have hg:=(grid_bounds pos b step degree count hbl hsl).1
  have hl:=CH2QRH.DensityComputation.verify_upper _ 0 (count-1) (-lo) cfg hprec hlo
  rw [Icc_zero_eq_range count hcount] at hl
  simp only [Expr.eval,cell_semantics,Finset.sum_neg_distrib,Rat.cast_neg] at hl
  linarith

theorem integral_upper_from_check (pos : Bool) (b step hi : ℚ) (degree count : ℕ)
    (hb : 0≤b) (hstep : 0≤step) (hcount : 0<count) (cfg : DyadicConfig)
    (hprec : cfg.precision≤0)
    (hhi : CH2QRH.DensityComputation.checkUpperBound
      (cellExpr true pos b step degree) 0 (count-1) hi cfg=true) :
    (∫y in (0:ℝ)..((step:ℝ)*count),moment pos b degree y)≤hi := by
  have hbl : (0:ℝ)≤b := by exact_mod_cast hb
  have hsl : (0:ℝ)≤step := by exact_mod_cast hstep
  have hg:=(grid_bounds pos b step degree count hbl hsl).2
  have hh:=CH2QRH.DensityComputation.verify_upper _ 0 (count-1) hi cfg hprec hhi
  rw [Icc_zero_eq_range count hcount] at hh
  simp only [cell_semantics] at hh
  exact hg.trans hh

#print axioms integral_lower_from_check
#print axioms integral_upper_from_check
end WinnerRivalMoments
