/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ReciprocalScalars
import DigammaIntegral
import MobiusSmoothing
import PerronPower
import WeightedMobius
import StripScalars

set_option pp.universes false
#print axioms RHContinuation.ReciprocalScalars.log_height_bound
#print axioms RHContinuation.ReciprocalScalars.log_compact_ratio_bound
#print axioms RHContinuation.ReciprocalScalars.compact_budget_lt_180
#print axioms RHContinuation.ReciprocalScalars.log_global_ratio_bound
#print axioms RHContinuation.ReciprocalScalars.exp_six_point_two_lt
#print axioms RHContinuation.ReciprocalScalars.six_rpow_point32_lt_two
#print axioms RHContinuation.ReciprocalScalars.global_budget_le
#print axioms RHContinuation.DigammaIntegral.kernel_bounds
#print axioms RHContinuation.DigammaIntegral.remainder_norm_le
#print axioms RHContinuation.DigammaIntegral.digamma_sub_log_bound
#print axioms RHContinuation.DigammaIntegral.digamma_real_lower
#print axioms RHContinuation.MobiusSmoothing.smoothing_identity
#print axioms RHContinuation.MobiusSmoothing.moebius_abs_le_one
#print axioms RHContinuation.MobiusSmoothing.newTerms_bound
#print axioms RHContinuation.MobiusSmoothing.smoothing_discrepancy
#print axioms RHContinuation.PerronPower.h_bounds
#print axioms RHContinuation.PerronPower.height_bounds
#print axioms RHContinuation.PerronPower.middle_power
#print axioms RHContinuation.PerronPower.high_power
#print axioms RHContinuation.PerronPower.coefficient_lt
#print axioms RHContinuation.PerronPower.actual_M_from_three_enclosures
#print axioms RHContinuation.WeightedMobius.weighted_from_actual_M
#print axioms RHContinuation.WeightedMobius.weighted_power_candidate_consumer
#print axioms RHContinuation.StripScalars.uniform_strip
#print axioms RHContinuation.StripScalars.global_budget_small

set_option pp.universes true
#print RHContinuation.PerronPower.actual_M_from_three_enclosures
#print RHContinuation.WeightedMobius.weighted_power_candidate_consumer
