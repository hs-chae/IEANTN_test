/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Nodes.RHPrimeCounting.v1.Conclusions
import ActualGMClosed
namespace RHPrimeCounting.v1
open Real IEANTN RHContinuation.Ramanujan
set_option maxHeartbeats 0
lemma source_eq : gm_source = GM_Q_Theorem1_1 := rfl
lemma provider_domain {x : ℝ} (hx : exp 35 ≤ x) : exp 8 ≤ x :=
  (exp_le_exp.mpr (by norm_num : (8:ℝ) ≤ 35)).trans hx

theorem challenge_prime_power_series : prime_power_series := by
  intro x hx
  exact actual_prime_power_series hx

theorem challenge_prime_power_nonnegative : prime_power_nonnegative := by
  intro x hx
  exact actual_prime_power_nonnegative hx

theorem challenge_generic_transfer (rh : RH.v1.hypothesis) (gm : gm_source)
    (hp : Buthe.v1.theorem_2_psi) (hj : Buthe.v1.theorem_2_li_minus_riemann_pi) :
    generic_transfer := by
  intro x hx
  exact actual_pi_closed_GM rh gm hp hj hx

theorem challenge_boxed_signed (rh : RH.v1.hypothesis) (gm : gm_source)
    (hp : Buthe.v1.theorem_2_psi) (hj : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (box : RHSmoothing.v1.box_psi) : boxed_signed := by
  intro x hx
  simpa [radius,transferCorrection,primePowerCorrection,add_assoc] using
    actual_pi_signed_profile rh gm hp hj IEANTN.RHSmoothing.fastBound
      (provider_domain hx) (box x hx)

theorem challenge_boxed_absolute (rh : RH.v1.hypothesis) (gm : gm_source)
    (hp : Buthe.v1.theorem_2_psi) (hj : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (box : RHSmoothing.v1.box_psi) : boxed_absolute := by
  intro x hx
  simpa [absoluteEnvelope,radius,transferCorrection,primePowerCorrection,add_assoc] using
    actual_pi_absolute_Li_profile rh gm hp hj IEANTN.RHSmoothing.fastBound
      (provider_domain hx) (box x hx)

theorem challenge_B5_absolute (rh : RH.v1.hypothesis) (gm : gm_source)
    (hp : Buthe.v1.theorem_2_psi) (hj : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (old : RHSmoothing.v1.B5_psi) : B5_absolute := by
  intro x hx
  simpa [absoluteEnvelope,radius,transferCorrection,primePowerCorrection,add_assoc] using
    actual_pi_absolute_Li_profile rh gm hp hj
      (IEANTN.RHSmoothing.envelope (831/1000) (287/500)) (provider_domain hx) (old x hx)

theorem challenge_boxed_strict_gain (gain : RHSmoothing.v1.box_improves_B5) : boxed_strict_gain := by
  intro x hx
  have hx0 : 0 < x := (exp_pos 35).trans_le hx
  have hx1 : 1 < x := (one_lt_exp_iff.mpr (by norm_num : (0:ℝ)<35)).trans_le hx
  have hL : (35:ℝ) ≤ log x := by
    apply exp_le_exp.mp
    simpa only [exp_log hx0] using hx
  have hp : 0 < sqrt x/log x := div_pos (sqrt_pos.mpr hx0) (log_pos hx1)
  have h := mul_lt_mul_of_pos_left (gain (log x) hL) hp
  unfold absoluteEnvelope radius
  simp only [div_eq_mul_inv,mul_assoc] at h ⊢
  nlinarith

#print axioms challenge_prime_power_series
#print axioms challenge_prime_power_nonnegative
#print axioms challenge_generic_transfer
#print axioms challenge_boxed_signed
#print axioms challenge_boxed_absolute
#print axioms challenge_B5_absolute
#print axioms challenge_boxed_strict_gain
end RHPrimeCounting.v1
