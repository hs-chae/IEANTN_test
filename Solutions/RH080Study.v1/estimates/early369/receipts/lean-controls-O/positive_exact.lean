import EarlySolution
set_option autoImplicit false
open Real
example (hRH:RH.v1.hypothesis) (hS:SchoenfeldRHTheta.v1.refined_theta) (h₁:Buthe.v1.theorem_2_theta) (h₂:Buthe.v1.theorem_2_theta_lower) : ThetaCubePopulation.v3.cube_density_096699_from_369 := ThetaCubePopulation.v3.challenge_cube_density_096699_from_369 hRH hS h₁ h₂
