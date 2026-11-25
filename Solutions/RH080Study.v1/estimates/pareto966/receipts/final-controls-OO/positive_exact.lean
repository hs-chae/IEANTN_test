import ParetoSolution
set_option autoImplicit false
open Real
example (hRH:RH.v1.hypothesis) (hS:SchoenfeldRHTheta.v1.refined_theta) (h₁:Buthe.v1.theorem_2_theta) (h₂:Buthe.v1.theorem_2_theta_lower) : ThetaCubePopulation.v2.cube_density_09669924 := ThetaCubePopulation.v2.challenge_cube_density_09669924 hRH hS h₁ h₂
