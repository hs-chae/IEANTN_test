import Lean
import BoxAudit
import BoxFourierCoefficients
import BoxImproved
import BoxIntegrability
import BoxMellinBridge
import BoxMellinCoefficients
import BoxMellinNormalization
import BoxTail
import BoxTailScalars
import EvolvedPi
import GMComparison
import GMPair
import GMTransport
import NicolasBlock
import NicolasFourPoint
import NicolasMultipoint
import OcticMellinNormalize
import OcticTrivialNormalize
import BalancedCountCheck
import Corr607Cell0
import Corr607Cell1
import Corr607Cell2
import Corr607Cell3
import Corr607Cell4
import Corr607Cell5
import Corr607Cell6
import Corr607Result
import Corr610Cell0
import Corr610Cell1
import Corr610Cell2
import Corr610Cell3
import Corr610Result
import CorrStrongHigh0
import CorrStrongHigh1
import CorrStrongHigh2
import CorrStrongHigh3
import CorrStrongHigh4
import CorrStrongHigh5
import CorrStrongHigh6
import CorrStrongMid0
import CorrelatedNumeric
import HighLogInputs
import PairedRamInterface
import RamBandHigh
import RamBandLow
import RamBandMid
import RamCorrelatedCore
import RamFrontier607
import RamPushCore
import RamResult
import RamStrongOverlay
import SharpBase
import OcticBPTInfinite
import OcticBPTSpecialization
import OcticConvergence
import OcticDecay
import OcticDerivativeBounds
import OcticDerivativeMoments
import OcticExplicitFormula
import OcticFourierMollifier
import OcticGreenSource
import OcticIntegralLimits
import OcticMollifier
import OcticPhysicalWeight
import OcticPoleNormalization
import OcticPopulationLimit
import OcticTrivialSeries
import OcticZeroAllowance
import OcticZeroDecomposition
import OcticZeroPairing
import AbsTrapezoid
import EndpointBenchmark
import OcticLocalQuadrature
import OcticQuadrature
import OcticSecondDecay
import ExactChallengeTypes
import NodeProviders
import OcticNetworkEvolution
import OcticSourceEvolution
import PrimorialEvolution
import PublicNetworkEvolution
import RamanujanEvolution
import PublicLcmV5
import PublicNicolasV2
import PublicPrimeIntervalV3
import PublicPrimeKernelInputsV3
import PublicPrimeQuantileV2
import PublicPrimorialV3
import PublicRHPrimeCountingV3
import PublicRHSmoothingV2
import PublicRamanujanGapV5

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mods := #["AbsTrapezoid","BalancedCountCheck","BoxAudit","BoxFourierCoefficients","BoxImproved","BoxIntegrability","BoxMellinBridge","BoxMellinCoefficients","BoxMellinNormalization","BoxTail","BoxTailScalars","Corr607Cell0","Corr607Cell1","Corr607Cell2","Corr607Cell3","Corr607Cell4","Corr607Cell5","Corr607Cell6","Corr607Result","Corr610Cell0","Corr610Cell1","Corr610Cell2","Corr610Cell3","Corr610Result","CorrStrongHigh0","CorrStrongHigh1","CorrStrongHigh2","CorrStrongHigh3","CorrStrongHigh4","CorrStrongHigh5","CorrStrongHigh6","CorrStrongMid0","CorrelatedNumeric","EndpointBenchmark","EvolvedPi","ExactChallengeTypes","GMComparison","GMPair","GMTransport","HighLogInputs","NicolasBlock","NicolasFourPoint","NicolasMultipoint","NodeProviders","OcticBPTInfinite","OcticBPTSpecialization","OcticConvergence","OcticDecay","OcticDerivativeBounds","OcticDerivativeMoments","OcticExplicitFormula","OcticFourierMollifier","OcticGreenSource","OcticIntegralLimits","OcticLocalQuadrature","OcticMellinNormalize","OcticMollifier","OcticNetworkEvolution","OcticPhysicalWeight","OcticPoleNormalization","OcticPopulationLimit","OcticQuadrature","OcticSecondDecay","OcticSourceEvolution","OcticTrivialNormalize","OcticTrivialSeries","OcticZeroAllowance","OcticZeroDecomposition","OcticZeroPairing","PairedRamInterface","PrimorialEvolution","PublicNetworkEvolution","RamBandHigh","RamBandLow","RamBandMid","RamCorrelatedCore","RamFrontier607","RamPushCore","RamResult","RamStrongOverlay","RamanujanEvolution","SharpBase"]
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let mut count : Nat := 0
  for (name, idx) in env.const2ModIdx.toList do
    let modName := (env.header.moduleNames[idx.toNat]?).getD .anonymous
    if !mods.contains modName.toString then continue
    let some info := env.find? name | continue
    match info with
    | .thmInfo _ =>
      let axs ← collectAxioms name
      unless axs.all allowed.contains do
        throwError "Nonstandard proof axiom in {name}: {axs}"
      let row := Json.mkObj [("name",toJson name.toString),("module",toJson modName.toString),("axioms",toJson (axs.map Name.toString))]
      logInfo m!"RH_NEW_THEOREM {row.compress}"
      count := count+1
    | _ => pure ()
  unless count > 0 do throwError "No owned theorem audited"
  logInfo m!"RH_NEW_THEOREM_AUDIT_PASS {count}"

private partial def parameterUses : Lean.Expr → List (String × Bool)
  | .lam n _ body _ => (n.toString, body.hasLooseBVar 0) :: parameterUses body
  | .mdata _ body => parameterUses body
  | _ => []

run_cmd do
  let env ← getEnv
  match env.find? `Lcm.v5.challenge_box_growth with
  | some (.thmInfo d) =>
    let uses := parameterUses d.value
    let row := Json.mkObj [("theorem",toJson "Lcm.v5.challenge_box_growth"),("lambda_parameters",toJson (uses.map fun (n,b) => Json.mkObj [("name",toJson n),("used_in_body",toJson b)]))]
    logInfo m!"RH_BODY_PARAMETERS {row.compress}"
  | _ => throwError "Missing actual solution theorem Lcm.v5.challenge_box_growth"
  match env.find? `Lcm.v5.challenge_recovered_growth with
  | some (.thmInfo d) =>
    let uses := parameterUses d.value
    let row := Json.mkObj [("theorem",toJson "Lcm.v5.challenge_recovered_growth"),("lambda_parameters",toJson (uses.map fun (n,b) => Json.mkObj [("name",toJson n),("used_in_body",toJson b)]))]
    logInfo m!"RH_BODY_PARAMETERS {row.compress}"
  | _ => throwError "Missing actual solution theorem Lcm.v5.challenge_recovered_growth"
  match env.find? `Nicolas.v2.challenge_four_gain with
  | some (.thmInfo d) =>
    let uses := parameterUses d.value
    let row := Json.mkObj [("theorem",toJson "Nicolas.v2.challenge_four_gain"),("lambda_parameters",toJson (uses.map fun (n,b) => Json.mkObj [("name",toJson n),("used_in_body",toJson b)]))]
    logInfo m!"RH_BODY_PARAMETERS {row.compress}"
  | _ => throwError "Missing actual solution theorem Nicolas.v2.challenge_four_gain"
  match env.find? `Nicolas.v2.challenge_product_block with
  | some (.thmInfo d) =>
    let uses := parameterUses d.value
    let row := Json.mkObj [("theorem",toJson "Nicolas.v2.challenge_product_block"),("lambda_parameters",toJson (uses.map fun (n,b) => Json.mkObj [("name",toJson n),("used_in_body",toJson b)]))]
    logInfo m!"RH_BODY_PARAMETERS {row.compress}"
  | _ => throwError "Missing actual solution theorem Nicolas.v2.challenge_product_block"
  match env.find? `Nicolas.v2.challenge_product_four with
  | some (.thmInfo d) =>
    let uses := parameterUses d.value
    let row := Json.mkObj [("theorem",toJson "Nicolas.v2.challenge_product_four"),("lambda_parameters",toJson (uses.map fun (n,b) => Json.mkObj [("name",toJson n),("used_in_body",toJson b)]))]
    logInfo m!"RH_BODY_PARAMETERS {row.compress}"
  | _ => throwError "Missing actual solution theorem Nicolas.v2.challenge_product_four"
  match env.find? `Nicolas.v2.challenge_spectral_four with
  | some (.thmInfo d) =>
    let uses := parameterUses d.value
    let row := Json.mkObj [("theorem",toJson "Nicolas.v2.challenge_spectral_four"),("lambda_parameters",toJson (uses.map fun (n,b) => Json.mkObj [("name",toJson n),("used_in_body",toJson b)]))]
    logInfo m!"RH_BODY_PARAMETERS {row.compress}"
  | _ => throwError "Missing actual solution theorem Nicolas.v2.challenge_spectral_four"
  match env.find? `PrimeInterval.v3.challenge_count_215 with
  | some (.thmInfo d) =>
    let uses := parameterUses d.value
    let row := Json.mkObj [("theorem",toJson "PrimeInterval.v3.challenge_count_215"),("lambda_parameters",toJson (uses.map fun (n,b) => Json.mkObj [("name",toJson n),("used_in_body",toJson b)]))]
    logInfo m!"RH_BODY_PARAMETERS {row.compress}"
  | _ => throwError "Missing actual solution theorem PrimeInterval.v3.challenge_count_215"
  match env.find? `PrimeInterval.v3.challenge_count_family with
  | some (.thmInfo d) =>
    let uses := parameterUses d.value
    let row := Json.mkObj [("theorem",toJson "PrimeInterval.v3.challenge_count_family"),("lambda_parameters",toJson (uses.map fun (n,b) => Json.mkObj [("name",toJson n),("used_in_body",toJson b)]))]
    logInfo m!"RH_BODY_PARAMETERS {row.compress}"
  | _ => throwError "Missing actual solution theorem PrimeInterval.v3.challenge_count_family"
  match env.find? `PrimeKernelInputs.v3.challenge_octic_215_explicit_formula with
  | some (.thmInfo d) =>
    let uses := parameterUses d.value
    let row := Json.mkObj [("theorem",toJson "PrimeKernelInputs.v3.challenge_octic_215_explicit_formula"),("lambda_parameters",toJson (uses.map fun (n,b) => Json.mkObj [("name",toJson n),("used_in_body",toJson b)]))]
    logInfo m!"RH_BODY_PARAMETERS {row.compress}"
  | _ => throwError "Missing actual solution theorem PrimeKernelInputs.v3.challenge_octic_215_explicit_formula"
  match env.find? `PrimeKernelInputs.v3.challenge_octic_family_explicit_formula with
  | some (.thmInfo d) =>
    let uses := parameterUses d.value
    let row := Json.mkObj [("theorem",toJson "PrimeKernelInputs.v3.challenge_octic_family_explicit_formula"),("lambda_parameters",toJson (uses.map fun (n,b) => Json.mkObj [("name",toJson n),("used_in_body",toJson b)]))]
    logInfo m!"RH_BODY_PARAMETERS {row.compress}"
  | _ => throwError "Missing actual solution theorem PrimeKernelInputs.v3.challenge_octic_family_explicit_formula"
  match env.find? `PrimeQuantile.v2.challenge_octic_block with
  | some (.thmInfo d) =>
    let uses := parameterUses d.value
    let row := Json.mkObj [("theorem",toJson "PrimeQuantile.v2.challenge_octic_block"),("lambda_parameters",toJson (uses.map fun (n,b) => Json.mkObj [("name",toJson n),("used_in_body",toJson b)]))]
    logInfo m!"RH_BODY_PARAMETERS {row.compress}"
  | _ => throwError "Missing actual solution theorem PrimeQuantile.v2.challenge_octic_block"
  match env.find? `PrimeQuantile.v2.challenge_successive_cubes with
  | some (.thmInfo d) =>
    let uses := parameterUses d.value
    let row := Json.mkObj [("theorem",toJson "PrimeQuantile.v2.challenge_successive_cubes"),("lambda_parameters",toJson (uses.map fun (n,b) => Json.mkObj [("name",toJson n),("used_in_body",toJson b)]))]
    logInfo m!"RH_BODY_PARAMETERS {row.compress}"
  | _ => throwError "Missing actual solution theorem PrimeQuantile.v2.challenge_successive_cubes"
  match env.find? `Primorial.v3.challenge_box_growth with
  | some (.thmInfo d) =>
    let uses := parameterUses d.value
    let row := Json.mkObj [("theorem",toJson "Primorial.v3.challenge_box_growth"),("lambda_parameters",toJson (uses.map fun (n,b) => Json.mkObj [("name",toJson n),("used_in_body",toJson b)]))]
    logInfo m!"RH_BODY_PARAMETERS {row.compress}"
  | _ => throwError "Missing actual solution theorem Primorial.v3.challenge_box_growth"
  match env.find? `RHPrimeCounting.v3.challenge_box_Li with
  | some (.thmInfo d) =>
    let uses := parameterUses d.value
    let row := Json.mkObj [("theorem",toJson "RHPrimeCounting.v3.challenge_box_Li"),("lambda_parameters",toJson (uses.map fun (n,b) => Json.mkObj [("name",toJson n),("used_in_body",toJson b)]))]
    logInfo m!"RH_BODY_PARAMETERS {row.compress}"
  | _ => throwError "Missing actual solution theorem RHPrimeCounting.v3.challenge_box_Li"
  match env.find? `RHPrimeCounting.v3.challenge_box_interval with
  | some (.thmInfo d) =>
    let uses := parameterUses d.value
    let row := Json.mkObj [("theorem",toJson "RHPrimeCounting.v3.challenge_box_interval"),("lambda_parameters",toJson (uses.map fun (n,b) => Json.mkObj [("name",toJson n),("used_in_body",toJson b)]))]
    logInfo m!"RH_BODY_PARAMETERS {row.compress}"
  | _ => throwError "Missing actual solution theorem RHPrimeCounting.v3.challenge_box_interval"
  match env.find? `RHPrimeCounting.v3.challenge_ch_Li with
  | some (.thmInfo d) =>
    let uses := parameterUses d.value
    let row := Json.mkObj [("theorem",toJson "RHPrimeCounting.v3.challenge_ch_Li"),("lambda_parameters",toJson (uses.map fun (n,b) => Json.mkObj [("name",toJson n),("used_in_body",toJson b)]))]
    logInfo m!"RH_BODY_PARAMETERS {row.compress}"
  | _ => throwError "Missing actual solution theorem RHPrimeCounting.v3.challenge_ch_Li"
  match env.find? `RHPrimeCounting.v3.challenge_paired_transfer with
  | some (.thmInfo d) =>
    let uses := parameterUses d.value
    let row := Json.mkObj [("theorem",toJson "RHPrimeCounting.v3.challenge_paired_transfer"),("lambda_parameters",toJson (uses.map fun (n,b) => Json.mkObj [("name",toJson n),("used_in_body",toJson b)]))]
    logInfo m!"RH_BODY_PARAMETERS {row.compress}"
  | _ => throwError "Missing actual solution theorem RHPrimeCounting.v3.challenge_paired_transfer"
  match env.find? `RHPrimeCounting.v3.challenge_refined_transfer with
  | some (.thmInfo d) =>
    let uses := parameterUses d.value
    let row := Json.mkObj [("theorem",toJson "RHPrimeCounting.v3.challenge_refined_transfer"),("lambda_parameters",toJson (uses.map fun (n,b) => Json.mkObj [("name",toJson n),("used_in_body",toJson b)]))]
    logInfo m!"RH_BODY_PARAMETERS {row.compress}"
  | _ => throwError "Missing actual solution theorem RHPrimeCounting.v3.challenge_refined_transfer"
  match env.find? `RHPrimeCounting.v3.challenge_transfer_gain with
  | some (.thmInfo d) =>
    let uses := parameterUses d.value
    let row := Json.mkObj [("theorem",toJson "RHPrimeCounting.v3.challenge_transfer_gain"),("lambda_parameters",toJson (uses.map fun (n,b) => Json.mkObj [("name",toJson n),("used_in_body",toJson b)]))]
    logInfo m!"RH_BODY_PARAMETERS {row.compress}"
  | _ => throwError "Missing actual solution theorem RHPrimeCounting.v3.challenge_transfer_gain"
  match env.find? `RHSmoothing.v2.challenge_box_gain with
  | some (.thmInfo d) =>
    let uses := parameterUses d.value
    let row := Json.mkObj [("theorem",toJson "RHSmoothing.v2.challenge_box_gain"),("lambda_parameters",toJson (uses.map fun (n,b) => Json.mkObj [("name",toJson n),("used_in_body",toJson b)]))]
    logInfo m!"RH_BODY_PARAMETERS {row.compress}"
  | _ => throwError "Missing actual solution theorem RHSmoothing.v2.challenge_box_gain"
  match env.find? `RHSmoothing.v2.challenge_box_psi with
  | some (.thmInfo d) =>
    let uses := parameterUses d.value
    let row := Json.mkObj [("theorem",toJson "RHSmoothing.v2.challenge_box_psi"),("lambda_parameters",toJson (uses.map fun (n,b) => Json.mkObj [("name",toJson n),("used_in_body",toJson b)]))]
    logInfo m!"RH_BODY_PARAMETERS {row.compress}"
  | _ => throwError "Missing actual solution theorem RHSmoothing.v2.challenge_box_psi"
  match env.find? `RamanujanGap.v5.challenge_full_profile with
  | some (.thmInfo d) =>
    let uses := parameterUses d.value
    let row := Json.mkObj [("theorem",toJson "RamanujanGap.v5.challenge_full_profile"),("lambda_parameters",toJson (uses.map fun (n,b) => Json.mkObj [("name",toJson n),("used_in_body",toJson b)]))]
    logInfo m!"RH_BODY_PARAMETERS {row.compress}"
  | _ => throwError "Missing actual solution theorem RamanujanGap.v5.challenge_full_profile"
  match env.find? `RamanujanGap.v5.challenge_margin_607b with
  | some (.thmInfo d) =>
    let uses := parameterUses d.value
    let row := Json.mkObj [("theorem",toJson "RamanujanGap.v5.challenge_margin_607b"),("lambda_parameters",toJson (uses.map fun (n,b) => Json.mkObj [("name",toJson n),("used_in_body",toJson b)]))]
    logInfo m!"RH_BODY_PARAMETERS {row.compress}"
  | _ => throwError "Missing actual solution theorem RamanujanGap.v5.challenge_margin_607b"
  match env.find? `RamanujanGap.v5.challenge_profile_gain with
  | some (.thmInfo d) =>
    let uses := parameterUses d.value
    let row := Json.mkObj [("theorem",toJson "RamanujanGap.v5.challenge_profile_gain"),("lambda_parameters",toJson (uses.map fun (n,b) => Json.mkObj [("name",toJson n),("used_in_body",toJson b)]))]
    logInfo m!"RH_BODY_PARAMETERS {row.compress}"
  | _ => throwError "Missing actual solution theorem RamanujanGap.v5.challenge_profile_gain"
  match env.find? `RamanujanGap.v5.challenge_ramanujan with
  | some (.thmInfo d) =>
    let uses := parameterUses d.value
    let row := Json.mkObj [("theorem",toJson "RamanujanGap.v5.challenge_ramanujan"),("lambda_parameters",toJson (uses.map fun (n,b) => Json.mkObj [("name",toJson n),("used_in_body",toJson b)]))]
    logInfo m!"RH_BODY_PARAMETERS {row.compress}"
  | _ => throwError "Missing actual solution theorem RamanujanGap.v5.challenge_ramanujan"
  match env.find? `RamanujanGap.v5.challenge_retains_original_margin with
  | some (.thmInfo d) =>
    let uses := parameterUses d.value
    let row := Json.mkObj [("theorem",toJson "RamanujanGap.v5.challenge_retains_original_margin"),("lambda_parameters",toJson (uses.map fun (n,b) => Json.mkObj [("name",toJson n),("used_in_body",toJson b)]))]
    logInfo m!"RH_BODY_PARAMETERS {row.compress}"
  | _ => throwError "Missing actual solution theorem RamanujanGap.v5.challenge_retains_original_margin"
