/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import PublicRHSmoothing
import PublicPrimeInterval
import PublicPrimeQuantile
import PublicLcm
import PublicPrimorial
namespace RHContinuation.IndependentBinderReview
theorem RHSmoothing_v1_box_psi : RH.v1.hypothesis → RHSmoothingInputs.v1.box_explicit_formula → RHSmoothingInputs.v1.box_zero_estimate → RHSmoothingInputs.v1.box_moments → RHSmoothing.v1.box_psi := @RHSmoothing.v1.challenge_box_psi
#print axioms RHSmoothing_v1_box_psi
theorem RHSmoothing_v1_B5_psi : RH.v1.hypothesis → RHSmoothingInputs.v1.parabola_inputs → RHSmoothing.v1.B5_psi := @RHSmoothing.v1.challenge_B5_psi
#print axioms RHSmoothing_v1_B5_psi
theorem RHSmoothing_v1_box_improves_B5 : RHSmoothing.v1.box_improves_B5 := @RHSmoothing.v1.challenge_box_improves_B5
#print axioms RHSmoothing_v1_box_improves_B5
theorem RHSmoothing_v1_recovered_ch_psi : RH.v1.hypothesis → ZetaLogDerivValues.v1.logDeriv_laurent_alternating → ZetaLogDerivValues.v1.logDeriv_neg_one → ZetaLogDerivValues.v1.logDeriv_two → ZetaLogDerivValues.v1.logDeriv_three_halves → CotangentSeries.v1.cot_series_zeta_values → ZeroCount.v1.rvm_error_bound → ZeroCount.v1.rvm_error_small → ZetaHadamard.v1.logDeriv_partial_fractions → RHSmoothing.v1.recovered_ch_psi := @RHSmoothing.v1.challenge_recovered_ch_psi
#print axioms RHSmoothing_v1_recovered_ch_psi
theorem PrimeInterval_v2_count_215 : RH.v1.hypothesis → PrimeKernelInputs.v1.octic_215 → PrimeInterval.v2.count_215 := @PrimeInterval.v2.challenge_count_215
#print axioms PrimeInterval_v2_count_215
theorem PrimeInterval_v2_count_family : RH.v1.hypothesis → PrimeKernelInputs.v1.octic_family → PrimeInterval.v2.count_family := @PrimeInterval.v2.challenge_count_family
#print axioms PrimeInterval_v2_count_family
theorem PrimeQuantile_v1_octic_block : PrimeInterval.v2.count_215 → PrimeQuantile.v1.octic_block := @PrimeQuantile.v1.challenge_octic_block
#print axioms PrimeQuantile_v1_octic_block
theorem PrimeQuantile_v1_successive_cubes : PrimeInterval.v2.count_215 → PrimeQuantile.v1.successive_cubes := @PrimeQuantile.v1.challenge_successive_cubes
#print axioms PrimeQuantile_v1_successive_cubes
theorem Lcm_v4_box_growth : RHSmoothing.v1.box_psi → Lcm.v4.box_growth := @Lcm.v4.challenge_box_growth
#print axioms Lcm_v4_box_growth
theorem Lcm_v4_recovered_growth : RHSmoothing.v1.recovered_ch_psi → Lcm.v4.recovered_growth := @Lcm.v4.challenge_recovered_growth
#print axioms Lcm_v4_recovered_growth
theorem Primorial_v2_box_growth : RH.v1.hypothesis → Buthe2016.v1.theorem_2_psi → RHSmoothing.v1.box_psi → Primorial.v2.box_growth := @Primorial.v2.challenge_box_growth
#print axioms Primorial_v2_box_growth
end RHContinuation.IndependentBinderReview
