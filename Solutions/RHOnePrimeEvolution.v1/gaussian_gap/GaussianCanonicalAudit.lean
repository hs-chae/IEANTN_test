import Lean
import GaussianNumericalWitness
import GaussianCanonicalConsumers

open Lean Elab Command
private partial def leadingUses : Expr → List (String × Bool)
  | .lam n _ b _ => (n.toString,b.hasLooseBVar 0) :: leadingUses b
  | .mdata _ b => leadingUses b
  | _ => []
run_cmd do
  let env ← getEnv
  let roots := #[
    (`GaussianFourierWitness.v1.challenge_integral_fourier_witness, #[]),
    (`GaussianFourierWitness.v1.challenge_objective_witness, #["hNumeric"]),
    (`RHAsymptoticGaussian.v1.challenge_normalized_gap, #["hCMS","rh","hNumeric"]),
    (`RHAsymptoticGaussian.v1.challenge_gap_below_printed_2026, #["hgap"]),
    (`RHAsymptoticGaussian.v1.challenge_population_curve, #["hCMS","rh","hNumeric"]),
    (`RHAsymptoticGaussian.v1.challenge_population_count, #["hcurve"]),
    (`RHOnePrime.GaussianGap.gaussian_eligible, #[]),
    (`RHOnePrime.GaussianFourier.fourier_actual_physical, #[]),
    (`RHOnePrime.GaussianKernel.physical_norm_upper, #[]),
    (`RHOnePrime.GaussianKernel.physical_full_wings_upper, #[]),
    (`RHOnePrime.GaussianKernel.physicalF_zero_lower, #[])]
  let allowed := #[`propext,`Classical.choice,`Quot.sound]
  for (root,required) in roots do
    let some (.thmInfo info) := env.find? root | throwError "Missing actual Gaussian theorem {root}"
    let axs ← collectAxioms root
    unless axs.all allowed.contains do throwError "Nonstandard Gaussian closure axiom {root}: {axs}"
    let uses := leadingUses info.value
    for input in required do
      unless uses.any (fun p => p.1 == input && p.2) do
        throwError "Unconsumed actual Gaussian node/source input {root}:{input}"
    logInfo m!"GAUSSIAN_ROOT {root} axioms={axs} input_uses={uses}"
  let edges := #[
    (`GaussianFourierWitness.v1.challenge_integral_fourier_witness,`RHOnePrime.GaussianGap.gaussian_eligible),
    (`GaussianFourierWitness.v1.challenge_integral_fourier_witness,`RHOnePrime.GaussianKernel.physical_norm_upper),
    (`GaussianFourierWitness.v1.challenge_integral_fourier_witness,`RHOnePrime.GaussianKernel.physical_full_wings_upper),
    (`GaussianFourierWitness.v1.challenge_integral_fourier_witness,`RHOnePrime.GaussianKernel.physicalF_zero_lower),
    (`RHOnePrime.GaussianGap.gaussian_eligible,`RHOnePrime.GaussianFourier.fourier_actual_physical),
    (`RHOnePrime.GaussianGap.gaussian_eligible,`RHOnePrime.GaussianFourier.integrable_physicalF),
    (`RHOnePrime.GaussianGap.gaussian_eligible,`RHOnePrime.GaussianFourier.integrable_physicalG),
    (`RHOnePrime.GaussianGap.gaussian_eligible,`RHOnePrime.GaussianFourier.continuous_physicalF),
    (`RHOnePrime.GaussianGap.gaussian_eligible,`RHOnePrime.GaussianFourier.physicalF_even),
    (`RHAsymptoticGaussian.v1.challenge_normalized_gap,`RHOnePrime.CMSFunctional.gap_from_functional),
    (`RHAsymptoticGaussian.v1.challenge_population_curve,`RHOnePrime.CMSFunctional.population_from_functional),
    (`RHAsymptoticGaussian.v1.challenge_population_count,`RHOnePrime.CMSFunctional.eventual_count_of_good)]
  for (consumer,provider) in edges do
    let some (.thmInfo info) := env.find? consumer | throwError "Missing value consumer {consumer}"
    unless info.value.getUsedConstants.contains provider do
      throwError "Required actual FT/numerical/ANT value edge absent {consumer}->{provider}"
    logInfo m!"GAUSSIAN_VALUE_EDGE {consumer}->{provider}"
  logInfo m!"GAUSSIAN_CANONICAL_AUDIT_PASS roots={roots.size} edges={edges.size}"

example : GaussianFourierWitness.v1.integral_fourier_witness :=
  GaussianFourierWitness.v1.challenge_integral_fourier_witness
example : GaussianFourierWitness.v1.integral_fourier_witness →
    GaussianFourierWitness.v1.objective_witness := GaussianFourierWitness.v1.challenge_objective_witness
example : CMSFunctionalInput.v1.gap_reduction → RH.v1.hypothesis →
    GaussianFourierWitness.v1.objective_witness → RHAsymptoticGaussian.v1.normalized_gap :=
  RHAsymptoticGaussian.v1.challenge_normalized_gap
example : RHAsymptoticGaussian.v1.normalized_gap → RHAsymptoticGaussian.v1.gap_below_printed_2026 :=
  RHAsymptoticGaussian.v1.challenge_gap_below_printed_2026
example : CMSFunctionalInput.v1.population_reduction → RH.v1.hypothesis →
    GaussianFourierWitness.v1.objective_witness → RHAsymptoticGaussian.v1.population_curve :=
  RHAsymptoticGaussian.v1.challenge_population_curve
example : RHAsymptoticGaussian.v1.population_curve → RHAsymptoticGaussian.v1.population_count :=
  RHAsymptoticGaussian.v1.challenge_population_count

open Real Filter IEANTN.CMSFunctional
example : RHAsymptoticGaussian.v1.normalized_gap =
    (∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      (((Nat.nth Nat.Prime (n+1) : ℕ) : ℝ)-Nat.nth Nat.Prime n) /
        (Real.sqrt (Nat.nth Nat.Prime n : ℝ)*Real.log (Nat.nth Nat.Prime n : ℝ)) ≤
          (834021/1000000 : ℝ)+ε) := rfl
