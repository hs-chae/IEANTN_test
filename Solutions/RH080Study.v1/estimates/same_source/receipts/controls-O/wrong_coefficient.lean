import SameSourceSolution
set_option autoImplicit false
open Real
example (hf:PrimeInterval.v4.optimized_strict_family) : ∀ n:ℝ,exp 8≤n → (78147/100000:ℝ)*n^2/log n < ((IEANTN.PrimeWindows.primesBetween (n^3) ((n+1)^3)).card:ℝ) := PrimePowerPopulation.v2.challenge_cube_density_all_real hf
