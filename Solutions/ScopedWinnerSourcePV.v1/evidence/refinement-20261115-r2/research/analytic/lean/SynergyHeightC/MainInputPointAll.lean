/- All finite providers are discharged: actual source input declarations feed
the actual same-buffer point execution in each canonical main-loop frame.
Whole-loop reachability, accumulation and I/O are separate obligations. -/
import SynergyHeightC.MainInputPointComposition
import SourceHeightEdgesV1.All
import SourceMainFramesV1.AllExecution
namespace SynergyHeightC.MainInputPointAll
open ScopedC ScopedC.Machine ScopedNumerical
open SynergyAnalytic.HeightPoint
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem actual_prefix (i : Nat) (hi : i < logCellCount) (total : ProofBox) :
    ∃ c d, PointExecuteAPI.modelOutputs (MainInputPointComposition.input i)=some (c,d) ∧
    Loops.SeqRun (ArraySourceCalls.Eval SynergyC.Header.layout FullMainPrefix.service)
      (ArraySourceCalls.Declare SynergyC.Header.layout FullMainPrefix.service)
      truth ArraySourceCalls.Scope (PointExecuteAPI.loopStatements.take 4)
      (FullMainEdges.loopState total i)
      (.continuing (PointExecuteAPI.filled (FullMainFrame.base total i) c d)) := by
  obtain ⟨input,pair,defined,model,execution⟩ :=
    SourceMainFramesV1.AllExecution.executions i hi total
  have same : MainInputPointComposition.input i=input := by
    simp only [MainInputPointComposition.input,defined,Option.getD_some]
  rw [←same] at model execution
  exact ⟨pair.1,pair.2,model,
    MainInputPointComposition.source_prefix (SourceHeightEdgesV1.All.edges i hi)
      total pair.1 pair.2 execution⟩

theorem actual_endpoint (i : Nat) (hi : i < logCellCount) (total : ProofBox) :
    ∃ c d, PointExecuteAPI.modelOutputs (MainInputPointComposition.input i)=some (c,d) ∧
    Loops.SeqRun (ArraySourceCalls.Eval SynergyC.Header.layout FullMainPrefix.service)
      (ArraySourceCalls.Declare SynergyC.Header.layout FullMainPrefix.service)
      truth ArraySourceCalls.Scope (PointExecuteAPI.loopStatements.take 4)
      (FullMainEdges.loopState total i)
      (.continuing (PointExecuteAPI.filled (FullMainFrame.base total i) c d)) ∧
    Machine.read SynergyC.Header.layout
      (PointExecuteAPI.filled (FullMainFrame.base total i) c d) ⟨21,0,[]⟩=
      some (SynergyC.SourceIntervalMath.represented c) ∧
    Machine.read SynergyC.Header.layout
      (PointExecuteAPI.filled (FullMainFrame.base total i) c d) ⟨22,0,[]⟩=
      some (SynergyC.SourceIntervalMath.represented d) ∧
    SynergyBasis.RealBox.Contains 128 c (r184 (logEndpoint (i+1))) ∧
    SynergyBasis.RealBox.Contains 128 d (r186 (logEndpoint (i+1))) := by
  obtain ⟨input,pair,defined,model,execution⟩ :=
    SourceMainFramesV1.AllExecution.executions i hi total
  have same : MainInputPointComposition.input i=input := by
    simp only [MainInputPointComposition.input,defined,Option.getD_some]
  have contains := logCell_sound (Nat.succ_le_of_lt hi) defined
  rw [←same] at model execution contains
  exact ⟨pair.1,pair.2,model,
    MainInputPointComposition.source_prefix_enclosures
      (SourceHeightEdgesV1.All.edges i hi) total pair.1 pair.2 execution model contains⟩

#print axioms actual_prefix
#print axioms actual_endpoint
end SynergyHeightC.MainInputPointAll
