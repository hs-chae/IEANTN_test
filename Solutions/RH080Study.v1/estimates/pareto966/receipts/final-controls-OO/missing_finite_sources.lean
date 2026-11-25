import ParetoSolution
set_option autoImplicit false
open Real
example (hRH:RH.v1.hypothesis) (hS:SchoenfeldRHTheta.v1.refined_theta) : ThetaCubePopulation.v2.cube_density_09669924 := ThetaCubePopulation.v2.challenge_cube_density_09669924 hRH hS
