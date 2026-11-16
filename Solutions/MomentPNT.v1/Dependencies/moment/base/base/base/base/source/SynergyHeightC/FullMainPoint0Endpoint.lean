/- Unconditional interval interpretation at the actual first logarithmic
endpoint, consuming the SAME source output records of the actual main prefix. -/
import SynergyHeightC.FullMainPoint0Flow
import SynergyAnalytic.HeightPointLogGrid
namespace SynergyHeightC.FullMainPoint0Endpoint
open ScopedC ScopedC.Machine ScopedNumerical
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem right_grid : SynergyAnalytic.HeightPoint.logCell 1=some FullMainEdge.right := by
  decide +kernel

theorem right_contains : SynergyBasis.RealBox.Contains 128 FullMainEdge.right
    (SynergyAnalytic.HeightPoint.logEndpoint 1) :=
  SynergyAnalytic.HeightPoint.logCell_sound (by decide +kernel) right_grid

theorem actual_first_endpoint :
    ∃ c d after,
      Loops.SeqRun (ArraySourceCalls.Eval SynergyC.Header.layout FullMainPrefix.service)
        (ArraySourceCalls.Declare SynergyC.Header.layout FullMainPrefix.service) truth ArraySourceCalls.Scope
        (PointExecuteAPI.loopStatements.take 4) FullMainPrefix.prefixState (.continuing after) ∧
      Machine.read SynergyC.Header.layout after ⟨21,0,[]⟩=
        some (SynergyC.SourceIntervalMath.represented c) ∧
      Machine.read SynergyC.Header.layout after ⟨22,0,[]⟩=
        some (SynergyC.SourceIntervalMath.represented d) ∧
      SynergyBasis.RealBox.Contains 128 c
        (SynergyAnalytic.HeightPoint.r184 (SynergyAnalytic.HeightPoint.logEndpoint 1)) ∧
      SynergyBasis.RealBox.Contains 128 d
        (SynergyAnalytic.HeightPoint.r186 (SynergyAnalytic.HeightPoint.logEndpoint 1)) :=
  FullMainPoint0Flow.actual_first_loop_enclosures right_contains

#print axioms right_grid
#print axioms right_contains
#print axioms actual_first_endpoint
end SynergyHeightC.FullMainPoint0Endpoint
