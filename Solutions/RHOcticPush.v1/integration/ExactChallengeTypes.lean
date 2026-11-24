/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import NodeProviders
import PrimorialEvolution
import OcticSourceEvolution
import RamanujanEvolution

/-! The proposition and binders below are read verbatim from actual generated
Challenge sources, then discharged by the solution proof constants. No Challenge
module, and therefore no deliberate challenge admission, enters this environment. -/
example
    (rh_v1_hypothesis : RH.v1.hypothesis)
    (rhsmoothinginputs_v1_box_explicit_formula : RHSmoothingInputs.v1.box_explicit_formula)
    (rhsmoothinginputs_v1_box_zero_estimate : RHSmoothingInputs.v1.box_zero_estimate)
    (boxmellininputs_v1_first_moment : BoxMellinInputs.v1.first_moment)
    (boxmellininputs_v1_second_moment_identity : BoxMellinInputs.v1.second_moment_identity) :
    RHSmoothing.v2.box_psi :=
  @RHSmoothing.v2.challenge_box_psi rh_v1_hypothesis rhsmoothinginputs_v1_box_explicit_formula rhsmoothinginputs_v1_box_zero_estimate boxmellininputs_v1_first_moment boxmellininputs_v1_second_moment_identity

#print axioms RHSmoothing.v2.challenge_box_psi
example : RHSmoothing.v2.box_gain :=
  @RHSmoothing.v2.challenge_box_gain

#print axioms RHSmoothing.v2.challenge_box_gain
example
    (rh_v1_hypothesis : RH.v1.hypothesis)
    (nicolas_v1_spectral_bound : Nicolas.v1.spectral_bound) :
    Nicolas.v2.spectral_four :=
  @Nicolas.v2.challenge_spectral_four rh_v1_hypothesis nicolas_v1_spectral_bound

#print axioms Nicolas.v2.challenge_spectral_four
example
    (rh_v1_hypothesis : RH.v1.hypothesis)
    (nicolas_v1_log_f_upper_full : Nicolas.v1.log_f_upper_full)
    (nicolas_v2_spectral_four : Nicolas.v2.spectral_four) :
    Nicolas.v2.product_four :=
  @Nicolas.v2.challenge_product_four rh_v1_hypothesis nicolas_v1_log_f_upper_full nicolas_v2_spectral_four

#print axioms Nicolas.v2.challenge_product_four
example
    (nicolas_v2_product_four : Nicolas.v2.product_four) :
    Nicolas.v2.product_block :=
  @Nicolas.v2.challenge_product_block nicolas_v2_product_four

#print axioms Nicolas.v2.challenge_product_block
example : Nicolas.v2.four_gain :=
  @Nicolas.v2.challenge_four_gain

#print axioms Nicolas.v2.challenge_four_gain
example
    (rh_v1_hypothesis : RH.v1.hypothesis)
    (rhprimecounting_v1_gm_source : RHPrimeCounting.v1.gm_source)
    (buthe_v1_theorem_2_psi : Buthe.v1.theorem_2_psi)
    (buthe_v1_theorem_2_li_minus_riemann_pi : Buthe.v1.theorem_2_li_minus_riemann_pi) :
    RHPrimeCounting.v3.refined_transfer :=
  @RHPrimeCounting.v3.challenge_refined_transfer rh_v1_hypothesis rhprimecounting_v1_gm_source buthe_v1_theorem_2_psi buthe_v1_theorem_2_li_minus_riemann_pi

#print axioms RHPrimeCounting.v3.challenge_refined_transfer
example : RHPrimeCounting.v3.transfer_gain :=
  @RHPrimeCounting.v3.challenge_transfer_gain

#print axioms RHPrimeCounting.v3.challenge_transfer_gain
example
    (rh_v1_hypothesis : RH.v1.hypothesis)
    (rhprimecounting_v1_gm_source : RHPrimeCounting.v1.gm_source)
    (rhprimecounting_v3_refined_transfer : RHPrimeCounting.v3.refined_transfer) :
    RHPrimeCounting.v3.paired_transfer :=
  @RHPrimeCounting.v3.challenge_paired_transfer rh_v1_hypothesis rhprimecounting_v1_gm_source rhprimecounting_v3_refined_transfer

#print axioms RHPrimeCounting.v3.challenge_paired_transfer
example
    (rhprimecounting_v3_refined_transfer : RHPrimeCounting.v3.refined_transfer)
    (rhsmoothing_v2_box_psi : RHSmoothing.v2.box_psi) :
    RHPrimeCounting.v3.box_Li :=
  @RHPrimeCounting.v3.challenge_box_Li rhprimecounting_v3_refined_transfer rhsmoothing_v2_box_psi

#print axioms RHPrimeCounting.v3.challenge_box_Li
example
    (rhprimecounting_v3_refined_transfer : RHPrimeCounting.v3.refined_transfer)
    (rhsmoothing_v1_recovered_ch_psi : RHSmoothing.v1.recovered_ch_psi) :
    RHPrimeCounting.v3.ch_Li :=
  @RHPrimeCounting.v3.challenge_ch_Li rhprimecounting_v3_refined_transfer rhsmoothing_v1_recovered_ch_psi

#print axioms RHPrimeCounting.v3.challenge_ch_Li
example
    (rhprimecounting_v3_box_li : RHPrimeCounting.v3.box_Li) :
    RHPrimeCounting.v3.box_interval :=
  @RHPrimeCounting.v3.challenge_box_interval rhprimecounting_v3_box_li

#print axioms RHPrimeCounting.v3.challenge_box_interval
example
    (rhsmoothing_v2_box_psi : RHSmoothing.v2.box_psi) :
    Lcm.v5.box_growth :=
  @Lcm.v5.challenge_box_growth rhsmoothing_v2_box_psi

#print axioms Lcm.v5.challenge_box_growth
example
    (rhsmoothing_v1_recovered_ch_psi : RHSmoothing.v1.recovered_ch_psi) :
    Lcm.v5.recovered_growth :=
  @Lcm.v5.challenge_recovered_growth rhsmoothing_v1_recovered_ch_psi

#print axioms Lcm.v5.challenge_recovered_growth
example
    (rh_v1_hypothesis : RH.v1.hypothesis)
    (buthe2016_v1_theorem_2_psi : Buthe2016.v1.theorem_2_psi)
    (rhsmoothing_v2_box_psi : RHSmoothing.v2.box_psi) :
    Primorial.v3.box_growth :=
  @Primorial.v3.challenge_box_growth rh_v1_hypothesis buthe2016_v1_theorem_2_psi rhsmoothing_v2_box_psi

#print axioms Primorial.v3.challenge_box_growth
example
    (greensmooth_v1_formula : GreenSmooth.v1.formula)
    (nicolas_v1_spectral_bound : Nicolas.v1.spectral_bound) :
    PrimeKernelInputs.v3.octic_215_explicit_formula :=
  @PrimeKernelInputs.v3.challenge_octic_215_explicit_formula greensmooth_v1_formula nicolas_v1_spectral_bound

#print axioms PrimeKernelInputs.v3.challenge_octic_215_explicit_formula
example
    (greensmooth_v1_formula : GreenSmooth.v1.formula)
    (nicolas_v1_spectral_bound : Nicolas.v1.spectral_bound) :
    PrimeKernelInputs.v3.octic_family_explicit_formula :=
  @PrimeKernelInputs.v3.challenge_octic_family_explicit_formula greensmooth_v1_formula nicolas_v1_spectral_bound

#print axioms PrimeKernelInputs.v3.challenge_octic_family_explicit_formula
example
    (rh_v1_hypothesis : RH.v1.hypothesis)
    (primekernelinputs_v3_octic_215_explicit_formula : PrimeKernelInputs.v3.octic_215_explicit_formula)
    (primekernelinputs_v2_octic_215_zero_estimate : PrimeKernelInputs.v2.octic_215_zero_estimate) :
    PrimeInterval.v3.count_215 :=
  @PrimeInterval.v3.challenge_count_215 rh_v1_hypothesis primekernelinputs_v3_octic_215_explicit_formula primekernelinputs_v2_octic_215_zero_estimate

#print axioms PrimeInterval.v3.challenge_count_215
example
    (rh_v1_hypothesis : RH.v1.hypothesis)
    (primekernelinputs_v3_octic_family_explicit_formula : PrimeKernelInputs.v3.octic_family_explicit_formula)
    (primekernelinputs_v2_octic_family_zero_estimate : PrimeKernelInputs.v2.octic_family_zero_estimate) :
    PrimeInterval.v3.count_family :=
  @PrimeInterval.v3.challenge_count_family rh_v1_hypothesis primekernelinputs_v3_octic_family_explicit_formula primekernelinputs_v2_octic_family_zero_estimate

#print axioms PrimeInterval.v3.challenge_count_family
example
    (primeinterval_v3_count_215 : PrimeInterval.v3.count_215) :
    PrimeQuantile.v2.octic_block :=
  @PrimeQuantile.v2.challenge_octic_block primeinterval_v3_count_215

#print axioms PrimeQuantile.v2.challenge_octic_block
example
    (primeinterval_v3_count_215 : PrimeInterval.v3.count_215) :
    PrimeQuantile.v2.successive_cubes :=
  @PrimeQuantile.v2.challenge_successive_cubes primeinterval_v3_count_215

#print axioms PrimeQuantile.v2.challenge_successive_cubes
example
    (rhprimecounting_v3_paired_transfer : RHPrimeCounting.v3.paired_transfer)
    (rh_v1_hypothesis : RH.v1.hypothesis)
    (rhprimecounting_v1_gm_source : RHPrimeCounting.v1.gm_source)
    (buthe_v1_theorem_2_psi : Buthe.v1.theorem_2_psi)
    (buthe_v1_theorem_2_li_minus_riemann_pi : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (buthe_v1_table_1_interval_bounds : Buthe.v1.table_1_interval_bounds)
    (buthe_v1_table_2_interval_bounds : Buthe.v1.table_2_interval_bounds)
    (buthe_v1_theorem_2_li_minus_pi : Buthe.v1.theorem_2_li_minus_pi)
    (buthe_v1_theorem_2_li_gt_pi : Buthe.v1.theorem_2_li_gt_pi)
    (buthe2016_v1_theorem_2_li_minus_pi : Buthe2016.v1.theorem_2_li_minus_pi) :
    RamanujanGap.v5.margin_607b :=
  @RamanujanGap.v5.challenge_margin_607b rhprimecounting_v3_paired_transfer rh_v1_hypothesis rhprimecounting_v1_gm_source buthe_v1_theorem_2_psi buthe_v1_theorem_2_li_minus_riemann_pi buthe_v1_table_1_interval_bounds buthe_v1_table_2_interval_bounds buthe_v1_theorem_2_li_minus_pi buthe_v1_theorem_2_li_gt_pi buthe2016_v1_theorem_2_li_minus_pi

#print axioms RamanujanGap.v5.challenge_margin_607b
example
    (rhprimecounting_v3_paired_transfer : RHPrimeCounting.v3.paired_transfer)
    (rh_v1_hypothesis : RH.v1.hypothesis)
    (rhprimecounting_v1_gm_source : RHPrimeCounting.v1.gm_source)
    (buthe_v1_theorem_2_psi : Buthe.v1.theorem_2_psi)
    (buthe_v1_theorem_2_li_minus_riemann_pi : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (buthe_v1_table_1_interval_bounds : Buthe.v1.table_1_interval_bounds)
    (buthe_v1_table_2_interval_bounds : Buthe.v1.table_2_interval_bounds)
    (buthe_v1_theorem_2_li_minus_pi : Buthe.v1.theorem_2_li_minus_pi)
    (buthe_v1_theorem_2_li_gt_pi : Buthe.v1.theorem_2_li_gt_pi)
    (buthe2016_v1_theorem_2_li_minus_pi : Buthe2016.v1.theorem_2_li_minus_pi) :
    RamanujanGap.v5.full_profile :=
  @RamanujanGap.v5.challenge_full_profile rhprimecounting_v3_paired_transfer rh_v1_hypothesis rhprimecounting_v1_gm_source buthe_v1_theorem_2_psi buthe_v1_theorem_2_li_minus_riemann_pi buthe_v1_table_1_interval_bounds buthe_v1_table_2_interval_bounds buthe_v1_theorem_2_li_minus_pi buthe_v1_theorem_2_li_gt_pi buthe2016_v1_theorem_2_li_minus_pi

#print axioms RamanujanGap.v5.challenge_full_profile
example
    (ramanujangap_v5_margin_607b : RamanujanGap.v5.margin_607b) :
    RamanujanGap.v5.ramanujan :=
  @RamanujanGap.v5.challenge_ramanujan ramanujangap_v5_margin_607b

#print axioms RamanujanGap.v5.challenge_ramanujan
example : RamanujanGap.v5.retains_original_margin :=
  @RamanujanGap.v5.challenge_retains_original_margin

#print axioms RamanujanGap.v5.challenge_retains_original_margin
example : RamanujanGap.v5.profile_gain :=
  @RamanujanGap.v5.challenge_profile_gain

#print axioms RamanujanGap.v5.challenge_profile_gain
