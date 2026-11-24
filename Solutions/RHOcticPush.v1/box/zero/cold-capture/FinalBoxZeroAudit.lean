import BoxEndpointBPT
import BoxHSeries
import BoxPrefactor
import BoxTrigamma
import BoxZeroInflation
import BoxZeroPairing
import BoxZeroScalar
import GammaDamped
import GammaEuler
import StieltjesDerivative
import StieltjesFinite
import BoxEndpointInfinite
import BoxGammaSecond
import BoxHDerivative
import GammaQuadratic
import StieltjesRegular
import BoxGammaRealSecond
import BoxQuadraticTail
import BoxZeroKernel
import GammaMellin
import StieltjesConstant
import BoxDerivativeTransport
import BoxPositivePieces
import BoxPrefactorSecond
import BoxZeroMoments
import BoxZeroShift
import GammaScaling
import BoxPrefactorTaylor
import BoxScaledMoments
import BoxTransportMajorant
import BoxZeroPacket
import GammaBoxSeries
import BoxFactorization
import BoxLaurentProduct
import BoxPacketBound
import BoxUnshiftedBound
import BoxFirstMoment
import BoxSecondMoment
import BoxZeroScalarExtra
import BoxZeroEstimate

open Lean Elab Command

theorem cold_box_zero_exact
    (hN : NicolasContinuation.SourceNicolas119)
    (hB : RHOcticPush.BPTSourceEndpoint.SourceBPTOffOrdinate) :
    RHSmoothingInputs.v1.box_zero_estimate :=
  RHOcticPush.BoxZero.box_zero_estimate_offOrdinate hN hB

#check @cold_box_zero_exact

run_cmd do
  let env ← getEnv
  let mods := #["BoxEndpointBPT","BoxHSeries","BoxPrefactor","BoxTrigamma","BoxZeroInflation","BoxZeroPairing","BoxZeroScalar","GammaDamped","GammaEuler","StieltjesDerivative","StieltjesFinite","BoxEndpointInfinite","BoxGammaSecond","BoxHDerivative","GammaQuadratic","StieltjesRegular","BoxGammaRealSecond","BoxQuadraticTail","BoxZeroKernel","GammaMellin","StieltjesConstant","BoxDerivativeTransport","BoxPositivePieces","BoxPrefactorSecond","BoxZeroMoments","BoxZeroShift","GammaScaling","BoxPrefactorTaylor","BoxScaledMoments","BoxTransportMajorant","BoxZeroPacket","GammaBoxSeries","BoxFactorization","BoxLaurentProduct","BoxPacketBound","BoxUnshiftedBound","BoxFirstMoment","BoxSecondMoment","BoxZeroScalarExtra","BoxZeroEstimate"]
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let mut count : Nat := 0
  for (name, idx) in env.const2ModIdx.toList do
    let modName := (env.header.moduleNames[idx.toNat]?).getD .anonymous
    if !mods.contains modName.toString then continue
    let some (.thmInfo _) := env.find? name | continue
    let axs ← collectAxioms name
    unless axs.all allowed.contains do
      throwError "Unaccepted axiom {name}: {axs}"
    let row := Json.mkObj [("name",toJson name.toString),
      ("module",toJson modName.toString),
      ("axioms",toJson (axs.map Name.toString))]
    logInfo m!"RH_BOX_ZERO_THEOREM {row.compress}"
    count := count + 1
  unless count > 0 do throwError "Empty forty-source audit"
  let some (.thmInfo _) := env.find? `cold_box_zero_exact |
    throwError "Missing exact original Box zero consumer"
  let axs ← collectAxioms `cold_box_zero_exact
  unless axs.all allowed.contains do throwError "Final axiom {axs}"
  logInfo m!"RH_BOX_ZERO_AUDIT_PASS {count}"
