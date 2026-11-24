/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import NodeProviders
import NetworkConsumers

/-! Actual assembly from original source inputs. None of the newly installed
psi, pi, spectrum, product, interval or lcm conclusions is an assumed parameter. -/
namespace RHOcticPush.Network

noncomputable def completedNetwork : Prop :=
  RHSmoothing.v2.box_psi ∧ RHSmoothing.v2.box_gain ∧
  RHPrimeCounting.v3.refined_transfer ∧ RHPrimeCounting.v3.transfer_gain ∧
  RHPrimeCounting.v3.paired_transfer ∧ RHPrimeCounting.v3.box_Li ∧
  RHPrimeCounting.v3.ch_Li ∧ RHPrimeCounting.v3.box_interval ∧
  Nicolas.v2.spectral_four ∧ Nicolas.v2.product_four ∧ Nicolas.v2.product_block ∧
  Nicolas.v2.four_gain ∧ Lcm.v5.box_growth ∧ Lcm.v5.recovered_growth

/-- The final14-node-conclusion consumer actually constructs every provider. -/
theorem full_network (rh : RH.v1.hypothesis)
    (hgm : RHPrimeCounting.v1.gm_source)
    (hp : Buthe.v1.theorem_2_psi) (hj : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hef : RHSmoothingInputs.v1.box_explicit_formula)
    (hz : RHSmoothingInputs.v1.box_zero_estimate)
    (hfirst : BoxMellinInputs.v1.first_moment)
    (hsecond : BoxMellinInputs.v1.second_moment_identity)
    (h119 : Nicolas.v1.spectral_bound) (h219 : Nicolas.v1.log_f_upper_full)
    (hk : ZetaLogDerivValues.v1.logDeriv_laurent_alternating)
    (hn : ZetaLogDerivValues.v1.logDeriv_neg_one)
    (h2 : ZetaLogDerivValues.v1.logDeriv_two)
    (hv : ZetaLogDerivValues.v1.logDeriv_three_halves)
    (hc : CotangentSeries.v1.cot_series_zeta_values)
    (hr : ZeroCount.v1.rvm_error_bound) (hs : ZeroCount.v1.rvm_error_small)
    (hh : ZetaHadamard.v1.logDeriv_partial_fractions) : completedNetwork := by
  have box := RHSmoothing.v2.challenge_box_psi rh hef hz hfirst hsecond
  have transfer := RHPrimeCounting.v3.challenge_refined_transfer rh hgm hp hj
  have pair := RHPrimeCounting.v3.challenge_paired_transfer rh hgm transfer
  have piBox := RHPrimeCounting.v3.challenge_box_Li transfer box
  have interval := RHPrimeCounting.v3.challenge_box_interval piBox
  have spectrum := Nicolas.v2.challenge_spectral_four rh h119
  have products := Nicolas.v2.challenge_product_four rh h219 spectrum
  have selector := Nicolas.v2.challenge_product_block products
  have ch := RHContinuation.Network.recovered_ch_psi rh hk hn h2 hv hc hr hs hh
  exact ⟨box,RHSmoothing.v2.challenge_box_gain,transfer,
    RHPrimeCounting.v3.challenge_transfer_gain,pair,piBox,
    RHPrimeCounting.v3.challenge_ch_Li transfer ch,interval,spectrum,products,selector,
    Nicolas.v2.challenge_four_gain,Lcm.v5.challenge_box_growth box,
    Lcm.v5.challenge_recovered_growth ch⟩

/-- With the same upstream hypotheses, the unchanged output interfaces still work. -/
theorem old_box_preserved (hi : RHSmoothing.v2.box_psi) : RHSmoothing.v1.box_psi := by
  intro x hx
  have h := hi x hx
  have he := RHSmoothing.v2.challenge_box_gain (Real.log x)
  have hp : (0:ℝ)<(1/25000)/Real.pi := by positivity
  exact h.trans (mul_le_mul_of_nonneg_left (by linarith) (Real.sqrt_nonneg x))

#print axioms full_network
#print axioms old_box_preserved
end RHOcticPush.Network
