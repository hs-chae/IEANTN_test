import Lean
import FinalSpectralAudit
import SpectralRamCore
import SpectralRam606Cells
import SpectralRamFrontier
import SpectralRamProfile
import ZeroInverseBand
import ZeroInversePaired
import IEANTN.Nodes.RamanujanGap.v6.Conclusions
import Ram606Network
import PublicRamanujanGapV6
import ExactRam606Types

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mods := #["SpectralRamCore","SpectralRam606Cells","SpectralRamFrontier","SpectralRamProfile","ZeroInverseBand","ZeroInversePaired","Ram606Network","ExactRam606Types"]
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let mut count : Nat := 0
  for (name, idx) in env.const2ModIdx.toList do
    let modName := (env.header.moduleNames[idx.toNat]?).getD .anonymous
    if !mods.contains modName.toString then continue
    let some (.thmInfo _) := env.find? name | continue
    let axs ← collectAxioms name
    unless axs.all allowed.contains do throwError "Nonstandard proof axiom {name}: {axs}"
    let row := Json.mkObj [("name",toJson name.toString),("module",toJson modName.toString),("axioms",toJson (axs.map Name.toString))]
    logInfo m!"RH_RAM606_FINAL_THEOREM {row.compress}"
    count := count + 1
  unless count > 0 do throwError "Empty completed Box audit"
  logInfo m!"RH_RAM606_FINAL_AUDIT_PASS {count}"

private partial def parameterUses : Lean.Expr → List (String × Bool)
  | .lam n _ body _ => (n.toString, body.hasLooseBVar 0) :: parameterUses body
  | .mdata _ body => parameterUses body
  | _ => []

run_cmd do
  let env ← getEnv
  let roots := #[`BoxMellinInputs.v2.challenge_first_moment,`BoxMellinInputs.v2.challenge_second_moment_identity,`BoxMellinInputs.v2.challenge_stieltjes_trapezoid,`Goldbach.v2.challenge_octic_fixed_sorted_count,`Goldbach.v2.challenge_octic_sorted_count,`Goldbach.v2.challenge_octic_sorted_family,`Lcm.v5.challenge_box_growth,`Lcm.v5.challenge_recovered_growth,`Lcm.v6.challenge_box_growth,`Nicolas.v2.challenge_four_gain,`Nicolas.v2.challenge_product_block,`Nicolas.v2.challenge_product_four,`Nicolas.v2.challenge_spectral_four,`PrimeInterval.v3.challenge_count_215,`PrimeInterval.v3.challenge_count_family,`PrimeInterval.v4.challenge_count_215,`PrimeInterval.v4.challenge_count_family,`PrimeInterval.v4.challenge_optimized_count_215,`PrimeInterval.v4.challenge_optimized_count_family,`PrimeInterval.v4.challenge_optimized_strict_215,`PrimeInterval.v4.challenge_optimized_strict_family,`PrimeInterval.v4.challenge_strict_214891875,`PrimeInterval.v4.challenge_strict_2149_uniform,`PrimeKernelInputs.v3.challenge_octic_215_explicit_formula,`PrimeKernelInputs.v3.challenge_octic_family_explicit_formula,`PrimeKernelInputs.v4.challenge_octic_215_zero_estimate,`PrimeKernelInputs.v4.challenge_octic_family_zero_estimate,`PrimeKernelInputs.v4.challenge_optimized_215_zero_estimate,`PrimeKernelInputs.v4.challenge_optimized_family_zero_estimate,`PrimeQuantile.v2.challenge_octic_block,`PrimeQuantile.v2.challenge_successive_cubes,`PrimeQuantile.v3.challenge_octic_block,`PrimeQuantile.v3.challenge_optimized_octic_block,`PrimeQuantile.v3.challenge_successive_cubes,`Primorial.v3.challenge_box_growth,`Primorial.v4.challenge_box_growth,`RHPrimeCounting.v3.challenge_box_Li,`RHPrimeCounting.v3.challenge_box_interval,`RHPrimeCounting.v3.challenge_ch_Li,`RHPrimeCounting.v3.challenge_paired_transfer,`RHPrimeCounting.v3.challenge_refined_transfer,`RHPrimeCounting.v3.challenge_transfer_gain,`RHPrimeCounting.v4.challenge_box_Li,`RHPrimeCounting.v4.challenge_box_interval,`RHPrimeCounting.v5.challenge_box_Li,`RHPrimeCounting.v5.challenge_box_interval,`RHPrimeCounting.v5.challenge_ch_Li,`RHPrimeCounting.v5.challenge_ch_interval,`RHPrimeCounting.v5.challenge_compensation_055,`RHPrimeCounting.v5.challenge_compensation_076,`RHPrimeCounting.v5.challenge_compensation_profile,`RHPrimeCounting.v5.challenge_effective_min,`RHPrimeCounting.v5.challenge_ordinary_transfer,`RHPrimeCounting.v5.challenge_whole_gain,`RHSmoothing.v2.challenge_box_gain,`RHSmoothing.v2.challenge_box_psi,`RHSmoothing.v3.challenge_box_gain,`RHSmoothing.v3.challenge_box_psi,`RHSmoothingInputs.v2.challenge_box_explicit_formula,`RHSmoothingInputs.v2.challenge_box_zero_estimate,`RamanujanGap.v5.challenge_full_profile,`RamanujanGap.v5.challenge_margin_607b,`RamanujanGap.v5.challenge_profile_gain,`RamanujanGap.v5.challenge_ramanujan,`RamanujanGap.v5.challenge_retains_original_margin,`RamanujanGap.v6.challenge_full_profile,`RamanujanGap.v6.challenge_local_606b,`RamanujanGap.v6.challenge_margin_606b,`RamanujanGap.v6.challenge_profile_gain,`RamanujanGap.v6.challenge_ramanujan,`RamanujanGap.v6.challenge_retains_original_margin,`RamanujanGap.v6.challenge_retains_v5_profile,`RHOcticPush.Network.fully_derived_box_network,`RHOcticPush.Network.fully_derived_spectral_box_network,`RHOcticPush.Network.fully_derived_spectral_ramanujan,`RHOcticPush.ZeroComparison.positive_inverse_band,`RHOcticPush.ZeroComparison.actual_both_sign_inverse_lower,`RHOcticPush.ZeroComparison.excludes_both_sign_sixteen]
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for root in roots do
    let some (.thmInfo info) := env.find? root | throwError "Missing theorem {root}"
    let axs ← collectAxioms root
    unless axs.all allowed.contains do throwError "Nonstandard final axiom {root}: {axs}"
    let ps := (parameterUses info.value).map fun (name,used) => Json.mkObj [("name",toJson name),("used_in_body",toJson used)]
    let row := Json.mkObj [("theorem",toJson root.toString),("lambda_parameters",toJson ps),("axioms",toJson (axs.map Name.toString))]
    logInfo m!"RH_RAM606_FINAL_BODY {row.compress}"
