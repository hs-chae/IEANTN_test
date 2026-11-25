import EarlySolution
set_option autoImplicit false
open Real
example (hRH:RH.v1.hypothesis) (hS:SchoenfeldRHTheta.v1.refined_theta) (h₁:Buthe.v1.theorem_2_theta) (h₂:Buthe.v1.theorem_2_theta_lower) : ∀ n:ℝ,369≤n → (967/1000:ℝ)*n^2/log n < ((IEANTN.ThetaWindows.openPrimes (n^3) ((n+1)^3)).card:ℝ) := ThetaCubePopulation.v3.challenge_cube_density_096699_from_369 hRH hS h₁ h₂
