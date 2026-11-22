/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import MertensProfile
import CubeCorrection
import CubeAbel
import CubeProfile
import NicolasBaseline
import Table13Check

set_option pp.universes false
#print axioms MertensPositive.first_mertens_square_profile
#print axioms MertensPositive.first_mertens_positive_earlier
#print axioms MertensPositive.first_mertens_positive_stronger
#print axioms MertensPositive.geometric_finite_tail_plus_cube
#print axioms MertensPositive.prime_finite_tail_plus_cube
#print axioms MertensPositive.finite_correction_by_base
#print axioms MertensPositive.finite_correction_reserves_cubes
#print axioms MertensPositive.fullTail_ge_square_add_cubes
#print axioms MertensPositive.theta_fourth_integrable
#print axioms MertensPositive.cubeFinite_abel
#print axioms MertensPositive.integral_cube_lower_model
#print axioms MertensPositive.finite_cube_lower
#print axioms MertensPositive.fullTail_ge_square_add_cubeFinite
#print axioms MertensPositive.first_mertens_cube_profile_u
#print axioms MertensPositive.cube_gain_lower_on_segment
#print axioms MertensPositive.cube_gain_lower
#print axioms MertensPositive.first_mertens_positive_cube
#print axioms MertensPositive.first_mertens_positive_cube_IEANTN
#print axioms NicolasContinuation.raw_product_pos
#print axioms NicolasContinuation.product_pos
#print axioms NicolasContinuation.theta_gt_one
#print axioms NicolasContinuation.log_ratio_eq
#print axioms NicolasContinuation.log_product_lower
#print axioms NicolasContinuation.relative_product_lower
#print axioms MertensPositive.first_mertens_at_seven_gt
#print axioms MertensPositive.table13_literal_caption_counterexample
#print axioms MertensPositive.seven_in_table13_first_row
set_option pp.universes true
#check @MertensPositive.first_mertens_positive_cube_IEANTN
#check @MertensPositive.first_mertens_positive_earlier
#check @NicolasContinuation.log_product_lower
#check @NicolasContinuation.relative_product_lower
#check @MertensPositive.table13_literal_caption_counterexample
