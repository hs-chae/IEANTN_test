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
import FinalSourceAudit
import FiniteApplicability
import GMUnsignedObstruction
import OcticBPTSourceEndpoint
import OcticEndpointSourceConsumer
import OcticFamilyMoments
import OcticFinalSourceConsumer
import OcticFourierMoments
import OcticMomentTransport
import OcticOptimizedCertified
import OcticStrictMoments
import OcticStrongerFrontier
import OcticTwoMomentsConsumer
import OcticFiniteQuadrature
import OcticLowMoment
import OcticMomentAssembly
import OcticTail
import OcticTailIntegrals
import GoldbachFinalSourceConsumer
import GoldbachTripleCount
import OcticGoldbachTripleCount
import ExactSupplementTypes
import OcticVerifiedEvolution
import BoxCDFConstruction
import BoxFourierSeries
import BoxPositiveMellin
import OcticEndpointChecker
import OcticEndpointData
import OcticEndpointSound
import OcticEndpointPilot
import OcticLogEndpointData
import OcticLogEndpointSound
import OcticCellData
import OcticCellSound
import OcticCellTotals
import OcticFiniteCaps
import OcticEndpointAssembly
import OcticCertifiedMoments
import OcticEndpointBlock000
import OcticEndpointBlock001
import OcticEndpointBlock002
import OcticEndpointBlock003
import OcticEndpointBlock004
import OcticEndpointBlock005
import OcticEndpointBlock006
import OcticEndpointBlock007
import OcticEndpointBlock008
import OcticEndpointBlock009
import OcticEndpointBlock010
import OcticEndpointBlock011
import OcticEndpointBlock012
import OcticEndpointBlock013
import OcticEndpointBlock014
import OcticEndpointBlock015
import OcticEndpointBlock016
import OcticEndpointBlock017
import OcticEndpointBlock018
import OcticEndpointBlock019
import OcticEndpointBlock020
import OcticEndpointBlock021
import OcticEndpointBlock022
import OcticEndpointBlock023
import OcticEndpointBlock024
import OcticEndpointBlock025
import OcticEndpointBlock026
import OcticEndpointBlock027
import OcticEndpointBlock028
import OcticEndpointBlock029
import OcticEndpointBlock030
import OcticEndpointBlock031
import OcticEndpointBlock032
import OcticEndpointBlock033
import OcticEndpointBlock034
import OcticEndpointBlock035
import OcticEndpointBlock036
import OcticEndpointBlock037
import OcticEndpointBlock038
import OcticEndpointBlock039
import OcticEndpointBlock040
import OcticEndpointBlock041
import OcticEndpointBlock042
import OcticEndpointBlock043
import OcticEndpointBlock044
import OcticEndpointBlock045
import OcticEndpointBlock046
import OcticEndpointBlock047
import OcticEndpointBlock048
import OcticEndpointBlock049
import OcticEndpointBlock050
import OcticEndpointBlock051
import OcticEndpointBlock052
import OcticEndpointBlock053
import OcticEndpointBlock054
import OcticEndpointBlock055
import OcticEndpointBlock056
import OcticEndpointBlock057
import OcticEndpointBlock058
import OcticEndpointBlock059
import OcticEndpointBlock060
import OcticEndpointBlock061
import OcticEndpointBlock062
import OcticEndpointBlock063
import OcticEndpointBlock064
import OcticEndpointBlock065
import OcticEndpointBlock066
import OcticEndpointBlock067
import OcticEndpointBlock068
import OcticEndpointBlock069
import OcticEndpointBlock070
import OcticEndpointBlock071
import OcticEndpointBlock072
import OcticEndpointBlock073
import OcticEndpointBlock074
import OcticEndpointBlock075
import OcticEndpointBlock076
import OcticEndpointBlock077
import OcticEndpointBlock078
import OcticEndpointBlock079
import OcticEndpointBlock080
import OcticEndpointBlock081
import OcticEndpointBlock082
import OcticEndpointBlock083
import OcticEndpointBlock084
import OcticEndpointBlock085
import OcticEndpointBlock086
import OcticEndpointBlock087
import OcticEndpointBlock088
import OcticEndpointBlock089
import OcticEndpointBlock090
import OcticEndpointBlock091
import OcticEndpointBlock092
import OcticEndpointBlock093
import OcticEndpointBlock094
import OcticEndpointBlock095
import OcticEndpointBlock096
import OcticEndpointBlock097
import OcticEndpointBlock098
import OcticEndpointBlock099
import OcticEndpointBlock100
import OcticEndpointBlock101
import OcticEndpointBlock102
import OcticEndpointBlock103
import OcticEndpointBlock104
import OcticEndpointBlock105
import OcticEndpointBlock106
import OcticEndpointBlock107
import OcticEndpointBlock108
import OcticEndpointBlock109
import OcticEndpointBlock110
import OcticEndpointBlock111
import OcticEndpointBlock112
import OcticEndpointBlock113
import OcticEndpointBlock114
import OcticStrongMomentCaps
import PublicGoldbachV2
import PublicPrimeIntervalV4
import PublicPrimeKernelInputsV4
import PublicPrimeQuantileV3

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mods := #["BoxCDFConstruction","BoxFourierSeries","BoxPositiveMellin","ExactSupplementTypes","FiniteApplicability","GMUnsignedObstruction","GoldbachFinalSourceConsumer","GoldbachTripleCount","OcticBPTSourceEndpoint","OcticCellData","OcticCellSound","OcticCellTotals","OcticCertifiedMoments","OcticEndpointAssembly","OcticEndpointBlock000","OcticEndpointBlock001","OcticEndpointBlock002","OcticEndpointBlock003","OcticEndpointBlock004","OcticEndpointBlock005","OcticEndpointBlock006","OcticEndpointBlock007","OcticEndpointBlock008","OcticEndpointBlock009","OcticEndpointBlock010","OcticEndpointBlock011","OcticEndpointBlock012","OcticEndpointBlock013","OcticEndpointBlock014","OcticEndpointBlock015","OcticEndpointBlock016","OcticEndpointBlock017","OcticEndpointBlock018","OcticEndpointBlock019","OcticEndpointBlock020","OcticEndpointBlock021","OcticEndpointBlock022","OcticEndpointBlock023","OcticEndpointBlock024","OcticEndpointBlock025","OcticEndpointBlock026","OcticEndpointBlock027","OcticEndpointBlock028","OcticEndpointBlock029","OcticEndpointBlock030","OcticEndpointBlock031","OcticEndpointBlock032","OcticEndpointBlock033","OcticEndpointBlock034","OcticEndpointBlock035","OcticEndpointBlock036","OcticEndpointBlock037","OcticEndpointBlock038","OcticEndpointBlock039","OcticEndpointBlock040","OcticEndpointBlock041","OcticEndpointBlock042","OcticEndpointBlock043","OcticEndpointBlock044","OcticEndpointBlock045","OcticEndpointBlock046","OcticEndpointBlock047","OcticEndpointBlock048","OcticEndpointBlock049","OcticEndpointBlock050","OcticEndpointBlock051","OcticEndpointBlock052","OcticEndpointBlock053","OcticEndpointBlock054","OcticEndpointBlock055","OcticEndpointBlock056","OcticEndpointBlock057","OcticEndpointBlock058","OcticEndpointBlock059","OcticEndpointBlock060","OcticEndpointBlock061","OcticEndpointBlock062","OcticEndpointBlock063","OcticEndpointBlock064","OcticEndpointBlock065","OcticEndpointBlock066","OcticEndpointBlock067","OcticEndpointBlock068","OcticEndpointBlock069","OcticEndpointBlock070","OcticEndpointBlock071","OcticEndpointBlock072","OcticEndpointBlock073","OcticEndpointBlock074","OcticEndpointBlock075","OcticEndpointBlock076","OcticEndpointBlock077","OcticEndpointBlock078","OcticEndpointBlock079","OcticEndpointBlock080","OcticEndpointBlock081","OcticEndpointBlock082","OcticEndpointBlock083","OcticEndpointBlock084","OcticEndpointBlock085","OcticEndpointBlock086","OcticEndpointBlock087","OcticEndpointBlock088","OcticEndpointBlock089","OcticEndpointBlock090","OcticEndpointBlock091","OcticEndpointBlock092","OcticEndpointBlock093","OcticEndpointBlock094","OcticEndpointBlock095","OcticEndpointBlock096","OcticEndpointBlock097","OcticEndpointBlock098","OcticEndpointBlock099","OcticEndpointBlock100","OcticEndpointBlock101","OcticEndpointBlock102","OcticEndpointBlock103","OcticEndpointBlock104","OcticEndpointBlock105","OcticEndpointBlock106","OcticEndpointBlock107","OcticEndpointBlock108","OcticEndpointBlock109","OcticEndpointBlock110","OcticEndpointBlock111","OcticEndpointBlock112","OcticEndpointBlock113","OcticEndpointBlock114","OcticEndpointChecker","OcticEndpointData","OcticEndpointPilot","OcticEndpointSound","OcticEndpointSourceConsumer","OcticFamilyMoments","OcticFinalSourceConsumer","OcticFiniteCaps","OcticFiniteQuadrature","OcticFourierMoments","OcticGoldbachTripleCount","OcticLogEndpointData","OcticLogEndpointSound","OcticLowMoment","OcticMomentAssembly","OcticMomentTransport","OcticOptimizedCertified","OcticStrictMoments","OcticStrongMomentCaps","OcticStrongerFrontier","OcticTail","OcticTailIntegrals","OcticTwoMomentsConsumer","OcticVerifiedEvolution"]
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let mut count : Nat := 0
  for (name, idx) in env.const2ModIdx.toList do
    let modName := (env.header.moduleNames[idx.toNat]?).getD .anonymous
    if !mods.contains modName.toString then continue
    let some (.thmInfo _) := env.find? name | continue
    let axs ← collectAxioms name
    unless axs.all allowed.contains do throwError "Nonstandard proof axiom {name}: {axs}"
    let row := Json.mkObj [("name",toJson name.toString),("module",toJson modName.toString),("axioms",toJson (axs.map Name.toString))]
    logInfo m!"RH_SUPPLEMENT_THEOREM {row.compress}"
    count := count + 1
  unless count > 0 do throwError "Empty supplement audit"
  logInfo m!"RH_SUPPLEMENT_AUDIT_PASS {count}"

private partial def parameterUses : Lean.Expr → List (String × Bool)
  | .lam n _ body _ => (n.toString, body.hasLooseBVar 0) :: parameterUses body
  | .mdata _ body => parameterUses body
  | _ => []

run_cmd do
  let env ← getEnv
  match env.find? `Goldbach.v2.challenge_octic_fixed_sorted_count with
  | some (.thmInfo d) =>
    let axs ← collectAxioms `Goldbach.v2.challenge_octic_fixed_sorted_count
    unless axs.all #[`propext, `Classical.choice, `Quot.sound].contains do throwError "Final root axiom Goldbach.v2.challenge_octic_fixed_sorted_count"
    let row := Json.mkObj [("theorem",toJson "Goldbach.v2.challenge_octic_fixed_sorted_count"),("lambda_parameters",toJson ((parameterUses d.value).map fun (n,b) => Json.mkObj [("name",toJson n),("used_in_body",toJson b)]))]
    logInfo m!"RH_SUPPLEMENT_BODY {row.compress}"
  | _ => throwError "Missing actual solution Goldbach.v2.challenge_octic_fixed_sorted_count"
  match env.find? `Goldbach.v2.challenge_octic_sorted_count with
  | some (.thmInfo d) =>
    let axs ← collectAxioms `Goldbach.v2.challenge_octic_sorted_count
    unless axs.all #[`propext, `Classical.choice, `Quot.sound].contains do throwError "Final root axiom Goldbach.v2.challenge_octic_sorted_count"
    let row := Json.mkObj [("theorem",toJson "Goldbach.v2.challenge_octic_sorted_count"),("lambda_parameters",toJson ((parameterUses d.value).map fun (n,b) => Json.mkObj [("name",toJson n),("used_in_body",toJson b)]))]
    logInfo m!"RH_SUPPLEMENT_BODY {row.compress}"
  | _ => throwError "Missing actual solution Goldbach.v2.challenge_octic_sorted_count"
  match env.find? `Goldbach.v2.challenge_octic_sorted_family with
  | some (.thmInfo d) =>
    let axs ← collectAxioms `Goldbach.v2.challenge_octic_sorted_family
    unless axs.all #[`propext, `Classical.choice, `Quot.sound].contains do throwError "Final root axiom Goldbach.v2.challenge_octic_sorted_family"
    let row := Json.mkObj [("theorem",toJson "Goldbach.v2.challenge_octic_sorted_family"),("lambda_parameters",toJson ((parameterUses d.value).map fun (n,b) => Json.mkObj [("name",toJson n),("used_in_body",toJson b)]))]
    logInfo m!"RH_SUPPLEMENT_BODY {row.compress}"
  | _ => throwError "Missing actual solution Goldbach.v2.challenge_octic_sorted_family"
  match env.find? `Lcm.v5.challenge_box_growth with
  | some (.thmInfo d) =>
    let axs ← collectAxioms `Lcm.v5.challenge_box_growth
    unless axs.all #[`propext, `Classical.choice, `Quot.sound].contains do throwError "Final root axiom Lcm.v5.challenge_box_growth"
    let row := Json.mkObj [("theorem",toJson "Lcm.v5.challenge_box_growth"),("lambda_parameters",toJson ((parameterUses d.value).map fun (n,b) => Json.mkObj [("name",toJson n),("used_in_body",toJson b)]))]
    logInfo m!"RH_SUPPLEMENT_BODY {row.compress}"
  | _ => throwError "Missing actual solution Lcm.v5.challenge_box_growth"
  match env.find? `Lcm.v5.challenge_recovered_growth with
  | some (.thmInfo d) =>
    let axs ← collectAxioms `Lcm.v5.challenge_recovered_growth
    unless axs.all #[`propext, `Classical.choice, `Quot.sound].contains do throwError "Final root axiom Lcm.v5.challenge_recovered_growth"
    let row := Json.mkObj [("theorem",toJson "Lcm.v5.challenge_recovered_growth"),("lambda_parameters",toJson ((parameterUses d.value).map fun (n,b) => Json.mkObj [("name",toJson n),("used_in_body",toJson b)]))]
    logInfo m!"RH_SUPPLEMENT_BODY {row.compress}"
  | _ => throwError "Missing actual solution Lcm.v5.challenge_recovered_growth"
  match env.find? `Nicolas.v2.challenge_four_gain with
  | some (.thmInfo d) =>
    let axs ← collectAxioms `Nicolas.v2.challenge_four_gain
    unless axs.all #[`propext, `Classical.choice, `Quot.sound].contains do throwError "Final root axiom Nicolas.v2.challenge_four_gain"
    let row := Json.mkObj [("theorem",toJson "Nicolas.v2.challenge_four_gain"),("lambda_parameters",toJson ((parameterUses d.value).map fun (n,b) => Json.mkObj [("name",toJson n),("used_in_body",toJson b)]))]
    logInfo m!"RH_SUPPLEMENT_BODY {row.compress}"
  | _ => throwError "Missing actual solution Nicolas.v2.challenge_four_gain"
  match env.find? `Nicolas.v2.challenge_product_block with
  | some (.thmInfo d) =>
    let axs ← collectAxioms `Nicolas.v2.challenge_product_block
    unless axs.all #[`propext, `Classical.choice, `Quot.sound].contains do throwError "Final root axiom Nicolas.v2.challenge_product_block"
    let row := Json.mkObj [("theorem",toJson "Nicolas.v2.challenge_product_block"),("lambda_parameters",toJson ((parameterUses d.value).map fun (n,b) => Json.mkObj [("name",toJson n),("used_in_body",toJson b)]))]
    logInfo m!"RH_SUPPLEMENT_BODY {row.compress}"
  | _ => throwError "Missing actual solution Nicolas.v2.challenge_product_block"
  match env.find? `Nicolas.v2.challenge_product_four with
  | some (.thmInfo d) =>
    let axs ← collectAxioms `Nicolas.v2.challenge_product_four
    unless axs.all #[`propext, `Classical.choice, `Quot.sound].contains do throwError "Final root axiom Nicolas.v2.challenge_product_four"
    let row := Json.mkObj [("theorem",toJson "Nicolas.v2.challenge_product_four"),("lambda_parameters",toJson ((parameterUses d.value).map fun (n,b) => Json.mkObj [("name",toJson n),("used_in_body",toJson b)]))]
    logInfo m!"RH_SUPPLEMENT_BODY {row.compress}"
  | _ => throwError "Missing actual solution Nicolas.v2.challenge_product_four"
  match env.find? `Nicolas.v2.challenge_spectral_four with
  | some (.thmInfo d) =>
    let axs ← collectAxioms `Nicolas.v2.challenge_spectral_four
    unless axs.all #[`propext, `Classical.choice, `Quot.sound].contains do throwError "Final root axiom Nicolas.v2.challenge_spectral_four"
    let row := Json.mkObj [("theorem",toJson "Nicolas.v2.challenge_spectral_four"),("lambda_parameters",toJson ((parameterUses d.value).map fun (n,b) => Json.mkObj [("name",toJson n),("used_in_body",toJson b)]))]
    logInfo m!"RH_SUPPLEMENT_BODY {row.compress}"
  | _ => throwError "Missing actual solution Nicolas.v2.challenge_spectral_four"
  match env.find? `PrimeInterval.v3.challenge_count_215 with
  | some (.thmInfo d) =>
    let axs ← collectAxioms `PrimeInterval.v3.challenge_count_215
    unless axs.all #[`propext, `Classical.choice, `Quot.sound].contains do throwError "Final root axiom PrimeInterval.v3.challenge_count_215"
    let row := Json.mkObj [("theorem",toJson "PrimeInterval.v3.challenge_count_215"),("lambda_parameters",toJson ((parameterUses d.value).map fun (n,b) => Json.mkObj [("name",toJson n),("used_in_body",toJson b)]))]
    logInfo m!"RH_SUPPLEMENT_BODY {row.compress}"
  | _ => throwError "Missing actual solution PrimeInterval.v3.challenge_count_215"
  match env.find? `PrimeInterval.v3.challenge_count_family with
  | some (.thmInfo d) =>
    let axs ← collectAxioms `PrimeInterval.v3.challenge_count_family
    unless axs.all #[`propext, `Classical.choice, `Quot.sound].contains do throwError "Final root axiom PrimeInterval.v3.challenge_count_family"
    let row := Json.mkObj [("theorem",toJson "PrimeInterval.v3.challenge_count_family"),("lambda_parameters",toJson ((parameterUses d.value).map fun (n,b) => Json.mkObj [("name",toJson n),("used_in_body",toJson b)]))]
    logInfo m!"RH_SUPPLEMENT_BODY {row.compress}"
  | _ => throwError "Missing actual solution PrimeInterval.v3.challenge_count_family"
  match env.find? `PrimeInterval.v4.challenge_count_215 with
  | some (.thmInfo d) =>
    let axs ← collectAxioms `PrimeInterval.v4.challenge_count_215
    unless axs.all #[`propext, `Classical.choice, `Quot.sound].contains do throwError "Final root axiom PrimeInterval.v4.challenge_count_215"
    let row := Json.mkObj [("theorem",toJson "PrimeInterval.v4.challenge_count_215"),("lambda_parameters",toJson ((parameterUses d.value).map fun (n,b) => Json.mkObj [("name",toJson n),("used_in_body",toJson b)]))]
    logInfo m!"RH_SUPPLEMENT_BODY {row.compress}"
  | _ => throwError "Missing actual solution PrimeInterval.v4.challenge_count_215"
  match env.find? `PrimeInterval.v4.challenge_count_family with
  | some (.thmInfo d) =>
    let axs ← collectAxioms `PrimeInterval.v4.challenge_count_family
    unless axs.all #[`propext, `Classical.choice, `Quot.sound].contains do throwError "Final root axiom PrimeInterval.v4.challenge_count_family"
    let row := Json.mkObj [("theorem",toJson "PrimeInterval.v4.challenge_count_family"),("lambda_parameters",toJson ((parameterUses d.value).map fun (n,b) => Json.mkObj [("name",toJson n),("used_in_body",toJson b)]))]
    logInfo m!"RH_SUPPLEMENT_BODY {row.compress}"
  | _ => throwError "Missing actual solution PrimeInterval.v4.challenge_count_family"
  match env.find? `PrimeInterval.v4.challenge_optimized_count_215 with
  | some (.thmInfo d) =>
    let axs ← collectAxioms `PrimeInterval.v4.challenge_optimized_count_215
    unless axs.all #[`propext, `Classical.choice, `Quot.sound].contains do throwError "Final root axiom PrimeInterval.v4.challenge_optimized_count_215"
    let row := Json.mkObj [("theorem",toJson "PrimeInterval.v4.challenge_optimized_count_215"),("lambda_parameters",toJson ((parameterUses d.value).map fun (n,b) => Json.mkObj [("name",toJson n),("used_in_body",toJson b)]))]
    logInfo m!"RH_SUPPLEMENT_BODY {row.compress}"
  | _ => throwError "Missing actual solution PrimeInterval.v4.challenge_optimized_count_215"
  match env.find? `PrimeInterval.v4.challenge_optimized_count_family with
  | some (.thmInfo d) =>
    let axs ← collectAxioms `PrimeInterval.v4.challenge_optimized_count_family
    unless axs.all #[`propext, `Classical.choice, `Quot.sound].contains do throwError "Final root axiom PrimeInterval.v4.challenge_optimized_count_family"
    let row := Json.mkObj [("theorem",toJson "PrimeInterval.v4.challenge_optimized_count_family"),("lambda_parameters",toJson ((parameterUses d.value).map fun (n,b) => Json.mkObj [("name",toJson n),("used_in_body",toJson b)]))]
    logInfo m!"RH_SUPPLEMENT_BODY {row.compress}"
  | _ => throwError "Missing actual solution PrimeInterval.v4.challenge_optimized_count_family"
  match env.find? `PrimeInterval.v4.challenge_optimized_strict_215 with
  | some (.thmInfo d) =>
    let axs ← collectAxioms `PrimeInterval.v4.challenge_optimized_strict_215
    unless axs.all #[`propext, `Classical.choice, `Quot.sound].contains do throwError "Final root axiom PrimeInterval.v4.challenge_optimized_strict_215"
    let row := Json.mkObj [("theorem",toJson "PrimeInterval.v4.challenge_optimized_strict_215"),("lambda_parameters",toJson ((parameterUses d.value).map fun (n,b) => Json.mkObj [("name",toJson n),("used_in_body",toJson b)]))]
    logInfo m!"RH_SUPPLEMENT_BODY {row.compress}"
  | _ => throwError "Missing actual solution PrimeInterval.v4.challenge_optimized_strict_215"
  match env.find? `PrimeInterval.v4.challenge_optimized_strict_family with
  | some (.thmInfo d) =>
    let axs ← collectAxioms `PrimeInterval.v4.challenge_optimized_strict_family
    unless axs.all #[`propext, `Classical.choice, `Quot.sound].contains do throwError "Final root axiom PrimeInterval.v4.challenge_optimized_strict_family"
    let row := Json.mkObj [("theorem",toJson "PrimeInterval.v4.challenge_optimized_strict_family"),("lambda_parameters",toJson ((parameterUses d.value).map fun (n,b) => Json.mkObj [("name",toJson n),("used_in_body",toJson b)]))]
    logInfo m!"RH_SUPPLEMENT_BODY {row.compress}"
  | _ => throwError "Missing actual solution PrimeInterval.v4.challenge_optimized_strict_family"
  match env.find? `PrimeInterval.v4.challenge_strict_214891875 with
  | some (.thmInfo d) =>
    let axs ← collectAxioms `PrimeInterval.v4.challenge_strict_214891875
    unless axs.all #[`propext, `Classical.choice, `Quot.sound].contains do throwError "Final root axiom PrimeInterval.v4.challenge_strict_214891875"
    let row := Json.mkObj [("theorem",toJson "PrimeInterval.v4.challenge_strict_214891875"),("lambda_parameters",toJson ((parameterUses d.value).map fun (n,b) => Json.mkObj [("name",toJson n),("used_in_body",toJson b)]))]
    logInfo m!"RH_SUPPLEMENT_BODY {row.compress}"
  | _ => throwError "Missing actual solution PrimeInterval.v4.challenge_strict_214891875"
  match env.find? `PrimeInterval.v4.challenge_strict_2149_uniform with
  | some (.thmInfo d) =>
    let axs ← collectAxioms `PrimeInterval.v4.challenge_strict_2149_uniform
    unless axs.all #[`propext, `Classical.choice, `Quot.sound].contains do throwError "Final root axiom PrimeInterval.v4.challenge_strict_2149_uniform"
    let row := Json.mkObj [("theorem",toJson "PrimeInterval.v4.challenge_strict_2149_uniform"),("lambda_parameters",toJson ((parameterUses d.value).map fun (n,b) => Json.mkObj [("name",toJson n),("used_in_body",toJson b)]))]
    logInfo m!"RH_SUPPLEMENT_BODY {row.compress}"
  | _ => throwError "Missing actual solution PrimeInterval.v4.challenge_strict_2149_uniform"
  match env.find? `PrimeKernelInputs.v3.challenge_octic_215_explicit_formula with
  | some (.thmInfo d) =>
    let axs ← collectAxioms `PrimeKernelInputs.v3.challenge_octic_215_explicit_formula
    unless axs.all #[`propext, `Classical.choice, `Quot.sound].contains do throwError "Final root axiom PrimeKernelInputs.v3.challenge_octic_215_explicit_formula"
    let row := Json.mkObj [("theorem",toJson "PrimeKernelInputs.v3.challenge_octic_215_explicit_formula"),("lambda_parameters",toJson ((parameterUses d.value).map fun (n,b) => Json.mkObj [("name",toJson n),("used_in_body",toJson b)]))]
    logInfo m!"RH_SUPPLEMENT_BODY {row.compress}"
  | _ => throwError "Missing actual solution PrimeKernelInputs.v3.challenge_octic_215_explicit_formula"
  match env.find? `PrimeKernelInputs.v3.challenge_octic_family_explicit_formula with
  | some (.thmInfo d) =>
    let axs ← collectAxioms `PrimeKernelInputs.v3.challenge_octic_family_explicit_formula
    unless axs.all #[`propext, `Classical.choice, `Quot.sound].contains do throwError "Final root axiom PrimeKernelInputs.v3.challenge_octic_family_explicit_formula"
    let row := Json.mkObj [("theorem",toJson "PrimeKernelInputs.v3.challenge_octic_family_explicit_formula"),("lambda_parameters",toJson ((parameterUses d.value).map fun (n,b) => Json.mkObj [("name",toJson n),("used_in_body",toJson b)]))]
    logInfo m!"RH_SUPPLEMENT_BODY {row.compress}"
  | _ => throwError "Missing actual solution PrimeKernelInputs.v3.challenge_octic_family_explicit_formula"
  match env.find? `PrimeKernelInputs.v4.challenge_octic_215_zero_estimate with
  | some (.thmInfo d) =>
    let axs ← collectAxioms `PrimeKernelInputs.v4.challenge_octic_215_zero_estimate
    unless axs.all #[`propext, `Classical.choice, `Quot.sound].contains do throwError "Final root axiom PrimeKernelInputs.v4.challenge_octic_215_zero_estimate"
    let row := Json.mkObj [("theorem",toJson "PrimeKernelInputs.v4.challenge_octic_215_zero_estimate"),("lambda_parameters",toJson ((parameterUses d.value).map fun (n,b) => Json.mkObj [("name",toJson n),("used_in_body",toJson b)]))]
    logInfo m!"RH_SUPPLEMENT_BODY {row.compress}"
  | _ => throwError "Missing actual solution PrimeKernelInputs.v4.challenge_octic_215_zero_estimate"
  match env.find? `PrimeKernelInputs.v4.challenge_octic_family_zero_estimate with
  | some (.thmInfo d) =>
    let axs ← collectAxioms `PrimeKernelInputs.v4.challenge_octic_family_zero_estimate
    unless axs.all #[`propext, `Classical.choice, `Quot.sound].contains do throwError "Final root axiom PrimeKernelInputs.v4.challenge_octic_family_zero_estimate"
    let row := Json.mkObj [("theorem",toJson "PrimeKernelInputs.v4.challenge_octic_family_zero_estimate"),("lambda_parameters",toJson ((parameterUses d.value).map fun (n,b) => Json.mkObj [("name",toJson n),("used_in_body",toJson b)]))]
    logInfo m!"RH_SUPPLEMENT_BODY {row.compress}"
  | _ => throwError "Missing actual solution PrimeKernelInputs.v4.challenge_octic_family_zero_estimate"
  match env.find? `PrimeKernelInputs.v4.challenge_optimized_215_zero_estimate with
  | some (.thmInfo d) =>
    let axs ← collectAxioms `PrimeKernelInputs.v4.challenge_optimized_215_zero_estimate
    unless axs.all #[`propext, `Classical.choice, `Quot.sound].contains do throwError "Final root axiom PrimeKernelInputs.v4.challenge_optimized_215_zero_estimate"
    let row := Json.mkObj [("theorem",toJson "PrimeKernelInputs.v4.challenge_optimized_215_zero_estimate"),("lambda_parameters",toJson ((parameterUses d.value).map fun (n,b) => Json.mkObj [("name",toJson n),("used_in_body",toJson b)]))]
    logInfo m!"RH_SUPPLEMENT_BODY {row.compress}"
  | _ => throwError "Missing actual solution PrimeKernelInputs.v4.challenge_optimized_215_zero_estimate"
  match env.find? `PrimeKernelInputs.v4.challenge_optimized_family_zero_estimate with
  | some (.thmInfo d) =>
    let axs ← collectAxioms `PrimeKernelInputs.v4.challenge_optimized_family_zero_estimate
    unless axs.all #[`propext, `Classical.choice, `Quot.sound].contains do throwError "Final root axiom PrimeKernelInputs.v4.challenge_optimized_family_zero_estimate"
    let row := Json.mkObj [("theorem",toJson "PrimeKernelInputs.v4.challenge_optimized_family_zero_estimate"),("lambda_parameters",toJson ((parameterUses d.value).map fun (n,b) => Json.mkObj [("name",toJson n),("used_in_body",toJson b)]))]
    logInfo m!"RH_SUPPLEMENT_BODY {row.compress}"
  | _ => throwError "Missing actual solution PrimeKernelInputs.v4.challenge_optimized_family_zero_estimate"
  match env.find? `PrimeQuantile.v2.challenge_octic_block with
  | some (.thmInfo d) =>
    let axs ← collectAxioms `PrimeQuantile.v2.challenge_octic_block
    unless axs.all #[`propext, `Classical.choice, `Quot.sound].contains do throwError "Final root axiom PrimeQuantile.v2.challenge_octic_block"
    let row := Json.mkObj [("theorem",toJson "PrimeQuantile.v2.challenge_octic_block"),("lambda_parameters",toJson ((parameterUses d.value).map fun (n,b) => Json.mkObj [("name",toJson n),("used_in_body",toJson b)]))]
    logInfo m!"RH_SUPPLEMENT_BODY {row.compress}"
  | _ => throwError "Missing actual solution PrimeQuantile.v2.challenge_octic_block"
  match env.find? `PrimeQuantile.v2.challenge_successive_cubes with
  | some (.thmInfo d) =>
    let axs ← collectAxioms `PrimeQuantile.v2.challenge_successive_cubes
    unless axs.all #[`propext, `Classical.choice, `Quot.sound].contains do throwError "Final root axiom PrimeQuantile.v2.challenge_successive_cubes"
    let row := Json.mkObj [("theorem",toJson "PrimeQuantile.v2.challenge_successive_cubes"),("lambda_parameters",toJson ((parameterUses d.value).map fun (n,b) => Json.mkObj [("name",toJson n),("used_in_body",toJson b)]))]
    logInfo m!"RH_SUPPLEMENT_BODY {row.compress}"
  | _ => throwError "Missing actual solution PrimeQuantile.v2.challenge_successive_cubes"
  match env.find? `PrimeQuantile.v3.challenge_octic_block with
  | some (.thmInfo d) =>
    let axs ← collectAxioms `PrimeQuantile.v3.challenge_octic_block
    unless axs.all #[`propext, `Classical.choice, `Quot.sound].contains do throwError "Final root axiom PrimeQuantile.v3.challenge_octic_block"
    let row := Json.mkObj [("theorem",toJson "PrimeQuantile.v3.challenge_octic_block"),("lambda_parameters",toJson ((parameterUses d.value).map fun (n,b) => Json.mkObj [("name",toJson n),("used_in_body",toJson b)]))]
    logInfo m!"RH_SUPPLEMENT_BODY {row.compress}"
  | _ => throwError "Missing actual solution PrimeQuantile.v3.challenge_octic_block"
  match env.find? `PrimeQuantile.v3.challenge_optimized_octic_block with
  | some (.thmInfo d) =>
    let axs ← collectAxioms `PrimeQuantile.v3.challenge_optimized_octic_block
    unless axs.all #[`propext, `Classical.choice, `Quot.sound].contains do throwError "Final root axiom PrimeQuantile.v3.challenge_optimized_octic_block"
    let row := Json.mkObj [("theorem",toJson "PrimeQuantile.v3.challenge_optimized_octic_block"),("lambda_parameters",toJson ((parameterUses d.value).map fun (n,b) => Json.mkObj [("name",toJson n),("used_in_body",toJson b)]))]
    logInfo m!"RH_SUPPLEMENT_BODY {row.compress}"
  | _ => throwError "Missing actual solution PrimeQuantile.v3.challenge_optimized_octic_block"
  match env.find? `PrimeQuantile.v3.challenge_successive_cubes with
  | some (.thmInfo d) =>
    let axs ← collectAxioms `PrimeQuantile.v3.challenge_successive_cubes
    unless axs.all #[`propext, `Classical.choice, `Quot.sound].contains do throwError "Final root axiom PrimeQuantile.v3.challenge_successive_cubes"
    let row := Json.mkObj [("theorem",toJson "PrimeQuantile.v3.challenge_successive_cubes"),("lambda_parameters",toJson ((parameterUses d.value).map fun (n,b) => Json.mkObj [("name",toJson n),("used_in_body",toJson b)]))]
    logInfo m!"RH_SUPPLEMENT_BODY {row.compress}"
  | _ => throwError "Missing actual solution PrimeQuantile.v3.challenge_successive_cubes"
  match env.find? `Primorial.v3.challenge_box_growth with
  | some (.thmInfo d) =>
    let axs ← collectAxioms `Primorial.v3.challenge_box_growth
    unless axs.all #[`propext, `Classical.choice, `Quot.sound].contains do throwError "Final root axiom Primorial.v3.challenge_box_growth"
    let row := Json.mkObj [("theorem",toJson "Primorial.v3.challenge_box_growth"),("lambda_parameters",toJson ((parameterUses d.value).map fun (n,b) => Json.mkObj [("name",toJson n),("used_in_body",toJson b)]))]
    logInfo m!"RH_SUPPLEMENT_BODY {row.compress}"
  | _ => throwError "Missing actual solution Primorial.v3.challenge_box_growth"
  match env.find? `RHPrimeCounting.v3.challenge_box_Li with
  | some (.thmInfo d) =>
    let axs ← collectAxioms `RHPrimeCounting.v3.challenge_box_Li
    unless axs.all #[`propext, `Classical.choice, `Quot.sound].contains do throwError "Final root axiom RHPrimeCounting.v3.challenge_box_Li"
    let row := Json.mkObj [("theorem",toJson "RHPrimeCounting.v3.challenge_box_Li"),("lambda_parameters",toJson ((parameterUses d.value).map fun (n,b) => Json.mkObj [("name",toJson n),("used_in_body",toJson b)]))]
    logInfo m!"RH_SUPPLEMENT_BODY {row.compress}"
  | _ => throwError "Missing actual solution RHPrimeCounting.v3.challenge_box_Li"
  match env.find? `RHPrimeCounting.v3.challenge_box_interval with
  | some (.thmInfo d) =>
    let axs ← collectAxioms `RHPrimeCounting.v3.challenge_box_interval
    unless axs.all #[`propext, `Classical.choice, `Quot.sound].contains do throwError "Final root axiom RHPrimeCounting.v3.challenge_box_interval"
    let row := Json.mkObj [("theorem",toJson "RHPrimeCounting.v3.challenge_box_interval"),("lambda_parameters",toJson ((parameterUses d.value).map fun (n,b) => Json.mkObj [("name",toJson n),("used_in_body",toJson b)]))]
    logInfo m!"RH_SUPPLEMENT_BODY {row.compress}"
  | _ => throwError "Missing actual solution RHPrimeCounting.v3.challenge_box_interval"
  match env.find? `RHPrimeCounting.v3.challenge_ch_Li with
  | some (.thmInfo d) =>
    let axs ← collectAxioms `RHPrimeCounting.v3.challenge_ch_Li
    unless axs.all #[`propext, `Classical.choice, `Quot.sound].contains do throwError "Final root axiom RHPrimeCounting.v3.challenge_ch_Li"
    let row := Json.mkObj [("theorem",toJson "RHPrimeCounting.v3.challenge_ch_Li"),("lambda_parameters",toJson ((parameterUses d.value).map fun (n,b) => Json.mkObj [("name",toJson n),("used_in_body",toJson b)]))]
    logInfo m!"RH_SUPPLEMENT_BODY {row.compress}"
  | _ => throwError "Missing actual solution RHPrimeCounting.v3.challenge_ch_Li"
  match env.find? `RHPrimeCounting.v3.challenge_paired_transfer with
  | some (.thmInfo d) =>
    let axs ← collectAxioms `RHPrimeCounting.v3.challenge_paired_transfer
    unless axs.all #[`propext, `Classical.choice, `Quot.sound].contains do throwError "Final root axiom RHPrimeCounting.v3.challenge_paired_transfer"
    let row := Json.mkObj [("theorem",toJson "RHPrimeCounting.v3.challenge_paired_transfer"),("lambda_parameters",toJson ((parameterUses d.value).map fun (n,b) => Json.mkObj [("name",toJson n),("used_in_body",toJson b)]))]
    logInfo m!"RH_SUPPLEMENT_BODY {row.compress}"
  | _ => throwError "Missing actual solution RHPrimeCounting.v3.challenge_paired_transfer"
  match env.find? `RHPrimeCounting.v3.challenge_refined_transfer with
  | some (.thmInfo d) =>
    let axs ← collectAxioms `RHPrimeCounting.v3.challenge_refined_transfer
    unless axs.all #[`propext, `Classical.choice, `Quot.sound].contains do throwError "Final root axiom RHPrimeCounting.v3.challenge_refined_transfer"
    let row := Json.mkObj [("theorem",toJson "RHPrimeCounting.v3.challenge_refined_transfer"),("lambda_parameters",toJson ((parameterUses d.value).map fun (n,b) => Json.mkObj [("name",toJson n),("used_in_body",toJson b)]))]
    logInfo m!"RH_SUPPLEMENT_BODY {row.compress}"
  | _ => throwError "Missing actual solution RHPrimeCounting.v3.challenge_refined_transfer"
  match env.find? `RHPrimeCounting.v3.challenge_transfer_gain with
  | some (.thmInfo d) =>
    let axs ← collectAxioms `RHPrimeCounting.v3.challenge_transfer_gain
    unless axs.all #[`propext, `Classical.choice, `Quot.sound].contains do throwError "Final root axiom RHPrimeCounting.v3.challenge_transfer_gain"
    let row := Json.mkObj [("theorem",toJson "RHPrimeCounting.v3.challenge_transfer_gain"),("lambda_parameters",toJson ((parameterUses d.value).map fun (n,b) => Json.mkObj [("name",toJson n),("used_in_body",toJson b)]))]
    logInfo m!"RH_SUPPLEMENT_BODY {row.compress}"
  | _ => throwError "Missing actual solution RHPrimeCounting.v3.challenge_transfer_gain"
  match env.find? `RHSmoothing.v2.challenge_box_gain with
  | some (.thmInfo d) =>
    let axs ← collectAxioms `RHSmoothing.v2.challenge_box_gain
    unless axs.all #[`propext, `Classical.choice, `Quot.sound].contains do throwError "Final root axiom RHSmoothing.v2.challenge_box_gain"
    let row := Json.mkObj [("theorem",toJson "RHSmoothing.v2.challenge_box_gain"),("lambda_parameters",toJson ((parameterUses d.value).map fun (n,b) => Json.mkObj [("name",toJson n),("used_in_body",toJson b)]))]
    logInfo m!"RH_SUPPLEMENT_BODY {row.compress}"
  | _ => throwError "Missing actual solution RHSmoothing.v2.challenge_box_gain"
  match env.find? `RHSmoothing.v2.challenge_box_psi with
  | some (.thmInfo d) =>
    let axs ← collectAxioms `RHSmoothing.v2.challenge_box_psi
    unless axs.all #[`propext, `Classical.choice, `Quot.sound].contains do throwError "Final root axiom RHSmoothing.v2.challenge_box_psi"
    let row := Json.mkObj [("theorem",toJson "RHSmoothing.v2.challenge_box_psi"),("lambda_parameters",toJson ((parameterUses d.value).map fun (n,b) => Json.mkObj [("name",toJson n),("used_in_body",toJson b)]))]
    logInfo m!"RH_SUPPLEMENT_BODY {row.compress}"
  | _ => throwError "Missing actual solution RHSmoothing.v2.challenge_box_psi"
  match env.find? `RamanujanGap.v5.challenge_full_profile with
  | some (.thmInfo d) =>
    let axs ← collectAxioms `RamanujanGap.v5.challenge_full_profile
    unless axs.all #[`propext, `Classical.choice, `Quot.sound].contains do throwError "Final root axiom RamanujanGap.v5.challenge_full_profile"
    let row := Json.mkObj [("theorem",toJson "RamanujanGap.v5.challenge_full_profile"),("lambda_parameters",toJson ((parameterUses d.value).map fun (n,b) => Json.mkObj [("name",toJson n),("used_in_body",toJson b)]))]
    logInfo m!"RH_SUPPLEMENT_BODY {row.compress}"
  | _ => throwError "Missing actual solution RamanujanGap.v5.challenge_full_profile"
  match env.find? `RamanujanGap.v5.challenge_margin_607b with
  | some (.thmInfo d) =>
    let axs ← collectAxioms `RamanujanGap.v5.challenge_margin_607b
    unless axs.all #[`propext, `Classical.choice, `Quot.sound].contains do throwError "Final root axiom RamanujanGap.v5.challenge_margin_607b"
    let row := Json.mkObj [("theorem",toJson "RamanujanGap.v5.challenge_margin_607b"),("lambda_parameters",toJson ((parameterUses d.value).map fun (n,b) => Json.mkObj [("name",toJson n),("used_in_body",toJson b)]))]
    logInfo m!"RH_SUPPLEMENT_BODY {row.compress}"
  | _ => throwError "Missing actual solution RamanujanGap.v5.challenge_margin_607b"
  match env.find? `RamanujanGap.v5.challenge_profile_gain with
  | some (.thmInfo d) =>
    let axs ← collectAxioms `RamanujanGap.v5.challenge_profile_gain
    unless axs.all #[`propext, `Classical.choice, `Quot.sound].contains do throwError "Final root axiom RamanujanGap.v5.challenge_profile_gain"
    let row := Json.mkObj [("theorem",toJson "RamanujanGap.v5.challenge_profile_gain"),("lambda_parameters",toJson ((parameterUses d.value).map fun (n,b) => Json.mkObj [("name",toJson n),("used_in_body",toJson b)]))]
    logInfo m!"RH_SUPPLEMENT_BODY {row.compress}"
  | _ => throwError "Missing actual solution RamanujanGap.v5.challenge_profile_gain"
  match env.find? `RamanujanGap.v5.challenge_ramanujan with
  | some (.thmInfo d) =>
    let axs ← collectAxioms `RamanujanGap.v5.challenge_ramanujan
    unless axs.all #[`propext, `Classical.choice, `Quot.sound].contains do throwError "Final root axiom RamanujanGap.v5.challenge_ramanujan"
    let row := Json.mkObj [("theorem",toJson "RamanujanGap.v5.challenge_ramanujan"),("lambda_parameters",toJson ((parameterUses d.value).map fun (n,b) => Json.mkObj [("name",toJson n),("used_in_body",toJson b)]))]
    logInfo m!"RH_SUPPLEMENT_BODY {row.compress}"
  | _ => throwError "Missing actual solution RamanujanGap.v5.challenge_ramanujan"
  match env.find? `RamanujanGap.v5.challenge_retains_original_margin with
  | some (.thmInfo d) =>
    let axs ← collectAxioms `RamanujanGap.v5.challenge_retains_original_margin
    unless axs.all #[`propext, `Classical.choice, `Quot.sound].contains do throwError "Final root axiom RamanujanGap.v5.challenge_retains_original_margin"
    let row := Json.mkObj [("theorem",toJson "RamanujanGap.v5.challenge_retains_original_margin"),("lambda_parameters",toJson ((parameterUses d.value).map fun (n,b) => Json.mkObj [("name",toJson n),("used_in_body",toJson b)]))]
    logInfo m!"RH_SUPPLEMENT_BODY {row.compress}"
  | _ => throwError "Missing actual solution RamanujanGap.v5.challenge_retains_original_margin"
