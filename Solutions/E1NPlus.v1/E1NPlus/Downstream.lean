/- Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import E1NPlus.TightAll
import ForwardRamanujanUpdate.Assembly
namespace E1NPlus
open Real E1FrozenN
set_option maxHeartbeats 0
section
variable (hs:DirectCH2Inputs)
    (h:WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH:IEANTN.RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH:IEANTN.ZetaZeroFreeHalfPlane (7/8))
include hs h hRH hQRH
/-- The old Ramanujan consumer's PNT premise is now supplied, not assumed. -/
theorem refined_psi : QRHCH2.v5.psi_refined_bound := by
  intro x hx
  have hx0:0<x:=(exp_pos _).trans_le hx
  have hL:300 ≤ log x:=by simpa only [log_exp] using log_le_log (exp_pos _) hx
  have hsq:(300:ℝ)^2 ≤ log x^2:=sq_le_sq₀ (by norm_num) (by linarith) |>.mpr hL
  have hc:(9468285637/1000000000000:ℝ) ≤ (1/566)*log x^2:=by nlinarith
  exact (pair300 hs h hRH hQRH hx).1.trans
    (mul_le_mul_of_nonneg_right hc (rpow_nonneg hx0.le _))

theorem ramanujan : RamanujanGap.v2.paired ∧ RamanujanGap.v2.strict_allowance_improvement :=
  ForwardRamanujan.forward (refined_psi hs h hRH hQRH)
end
#print axioms refined_psi
#print axioms ramanujan
end E1NPlus
