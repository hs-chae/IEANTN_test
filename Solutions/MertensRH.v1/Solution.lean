/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Nodes.MertensRH.v1.Conclusions
import CubeProfile
namespace MertensRH.v1
 theorem challenge_positive_cube (hRH : RH.v1.hypothesis) (h154 : bfknw154) (h21 : bfknw21)
    (hPsi : Buthe.v1.theorem_2_psi) (hThetaL : Buthe.v1.theorem_2_theta)
    (hThetaU : Buthe.v1.theorem_2_theta_lower) : positive_cube := by
  intro x hx hxM
  exact MertensPositive.first_mertens_positive_cube_IEANTN h154 h21 hPsi hThetaL hThetaU hRH hx hxM
 theorem challenge_positive_earlier (hRH : RH.v1.hypothesis) (h154 : bfknw154) (h21 : bfknw21)
    (hPsi : Buthe.v1.theorem_2_psi) (hThetaL : Buthe.v1.theorem_2_theta)
    (hThetaU : Buthe.v1.theorem_2_theta_lower) : positive_earlier := by
  intro x hx hxM
  exact MertensPositive.first_mertens_positive_earlier h154 h21
    (MertensPositive.buthe_psi_adapter hPsi) (MertensPositive.buthe_theta_lower_adapter hThetaL)
    (MertensPositive.buthe_theta_upper_adapter hThetaU) hRH hx hxM
 theorem challenge_cube_profile (hRH : RH.v1.hypothesis) (h154 : bfknw154) (h21 : bfknw21)
    (hPsi : Buthe.v1.theorem_2_psi) (hThetaL : Buthe.v1.theorem_2_theta)
    (hThetaU : Buthe.v1.theorem_2_theta_lower) : cube_profile := by
  intro u hu hM
  have h := MertensPositive.first_mertens_cube_profile_u h154 h21
    (MertensPositive.buthe_psi_adapter hPsi) (MertensPositive.buthe_theta_lower_adapter hThetaL)
    (MertensPositive.buthe_theta_upper_adapter hThetaU) hRH hu hM
  convert h using 1 <;> first | rfl | (norm_num [MertensPositive.cubeGain])
#print axioms challenge_positive_cube
#print axioms challenge_positive_earlier
#print axioms challenge_cube_profile
end MertensRH.v1
