/- Actual C point outputs supply the existing conditional ANT consumers.
   The finite source provider is discharged; full main/weight/I/O is separate. -/
import SourceHeightPointsV2.All
import SynergyHeightC.SourcePNTFromSemanticOutputs
namespace SourceHeightPointsV2.PNT
open Real IEANTN WinnerOriginalScalars WinnerNewHeightSource WinnerDirectKernel
open SynergyAnalytic SynergyAnalytic.HeightPoint
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem source_pi_008441646
    (h : PrimaryInputs (3681/10000) (3599/10000))
    (hCHJ : OriginalCHJSource) (hrvm : ZeroCount.v1.rvm_error_bound)
    (hsmall : ZeroCount.v1.rvm_error_small)
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    (hRH : RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH : ZetaZeroFreeHalfPlane (7/8)) :
    HasPowerLogBound Eπ (8441646/1000000000) 0 (7/8) (Real.exp 330) :=
  SynergyHeightC.PointExecuteAPI.pi_008441646_of_source_outputs
    SourceHeightPointsV2.All.outputs h hCHJ hrvm hsmall hlow hRH hQRH

theorem source_prime_rich_017
    (h : PrimaryInputs (3681/10000) (3599/10000))
    (hCHJ : OriginalCHJSource) (hrvm : ZeroCount.v1.rvm_error_bound)
    (hsmall : ZeroCount.v1.rvm_error_small)
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    (hRH : RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH : ZetaZeroFreeHalfPlane (7/8))
    {x : ℝ} (hx : Real.exp 330 ≤ x) :
    (57/500000:ℝ)*x^((7:ℝ)/8)/Real.log x ≤
      primeCounting (x+(17/1000:ℝ)*x^((7:ℝ)/8))-primeCounting x :=
  SynergyHeightC.PointExecuteAPI.prime_rich_017_of_source_outputs
    SourceHeightPointsV2.All.outputs h hCHJ hrvm hsmall hlow hRH hQRH hx

end SourceHeightPointsV2.PNT
open Lean Elab
run_elab do
 let env ← getEnv
 for n in [`SourceHeightPointsV2.PNT.source_pi_008441646,
   `SourceHeightPointsV2.PNT.source_prime_rich_017] do
  let some ci := env.find? n | throwError "missing actual C/ANT consumer"
  let ax ← Lean.collectAxioms n
  let used := match ci with
   | .thmInfo v => v.value.getUsedConstants
   | _ => #[]
  unless used.contains `SourceHeightPointsV2.All.outputs do
   throwError "actual source provider absent from consumer proof"
  logInfo m!"SOURCE_PNT_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString)),("uses_actual768_source_provider",toJson true)]).compress}"
