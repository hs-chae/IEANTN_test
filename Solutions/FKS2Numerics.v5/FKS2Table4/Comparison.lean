/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FKS2Table4.Result
import IEANTN.Nodes.QRHPropagation.v2.Conclusions
namespace FKS2Table4
open Real IEANTN FKS2Scalar

theorem alternate_endpoint_check :
    (0.01323:ℚ)*(expHi (-10.3125))^4 < (5:ℚ)/10^16 := by native_decide

/-- The existing density route is stronger on this entire ray, under its additional inputs. -/
theorem alternate_route_stronger {x : ℝ} (hx : exp 330 ≤ x) :
    (0.01323:ℝ)*x^(-(1:ℝ)/8) < (5:ℝ)/10^16 := by
  have hx0 : 0<x := (exp_pos _).trans_le hx
  have hL : 330 ≤ log x := by simpa using log_le_log (exp_pos (330:ℝ)) hx
  have he := exp_pow_upper (n := 4) analytic_checks.2.2.1
  norm_num at he
  rw [rpow_def_of_pos hx0]
  have hm : exp (log x*(-(1:ℝ)/8)) ≤ exp (-(41.25:ℝ)) :=
    exp_le_exp.mpr (by linarith)
  have hend : (0.01323:ℝ)*(expHi (-10.3125):ℝ)^4 < (5:ℝ)/10^16 := by
    have h := (Rat.cast_lt (K := ℝ)).2 alternate_endpoint_check
    simpa only [Rat.cast_mul,Rat.cast_pow,Rat.cast_div,Rat.cast_ofScientific,
      Rat.cast_ofNat] using h
  have he' : exp (-(41.25:ℝ)) ≤ (expHi (-10.3125):ℝ)^4 := by
    convert he using 1 <;> norm_num
  exact (mul_le_mul_of_nonneg_left (hm.trans he') (by norm_num)).trans_lt hend

end FKS2Table4
