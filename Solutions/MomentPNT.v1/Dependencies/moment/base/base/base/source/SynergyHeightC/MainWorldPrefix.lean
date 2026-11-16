/- Pure actual source prefix and budget steps in the unchanged explicit I/O world. -/
import SynergyHeightC.MainInputPointComposition
import SynergyHeightC.MainBudgetExecute
import SynergyHeightC.EmitUSource
namespace SynergyHeightC.MainWorldPrefix
open ScopedC ScopedC.Syntax ScopedC.Machine ScopedNumerical
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 100000

theorem actual_point_prefix (service : ScopedIO.WorldIO.Call)
    (platform : ScopedIO.WorldIO.Platform) (stream : ScopedIO.Stream)
    {i : Nat} (edges : FullMainEdges.ExactEdges i) (total c d : ProofBox)
    (pointRun : FullContractPointExecute.run (FullMainFrame.base total i)
      (MainInputPointComposition.input i)=some
      (.unit,PointExecuteAPI.filled (FullMainFrame.base total i) c d)) :
    Loops.SeqRun (ScopedIO.WorldSource.Eval SynergyC.Header.layout FullMainPrefix.service
      service platform) (ScopedIO.WorldSource.Declare SynergyC.Header.layout FullMainPrefix.service)
      truth ScopedIO.WorldSource.Scope (PointExecuteAPI.loopStatements.take 4)
      ⟨FullMainEdges.loopState total i,stream⟩
      (.continuing ⟨PointExecuteAPI.filled (FullMainFrame.base total i) c d,stream⟩) := by
  have edgeEq : FullMainEdges.run total i=ArraySourceExecute.statements SynergyC.Header.layout
      FullMainPrefix.service 128 2048 FullMainEdge.statements (FullMainEdges.loopState total i) := by
    unfold FullMainEdges.run
    rfl
  have edgeRun := Eq.mp (congrArg (fun r=>r=some
    (.continuing (FullMainFrame.base total i))) edgeEq) (edges total)
  have first := (ScopedIO.WorldLift.pure_sound SynergyC.Header.layout FullMainPrefix.service
    service platform stream 128 2048).2.1 FullMainEdge.statements (FullMainEdges.loopState total i)
      (.continuing (FullMainFrame.base total i)) edgeRun
  have pointEq : FullContractPointExecute.run (FullMainFrame.base total i)
      (MainInputPointComposition.input i)=FullMainPrefix.service "pointHeight"
      (PointExecuteAPI.args (FullMainFrame.base total i) (MainInputPointComposition.input i))
      (PointExecuteAPI.buffers (FullMainFrame.base total i)) := by
    unfold FullContractPointExecute.run
    rfl
  have called := Eq.mp (congrArg (fun r=>r=some
    (.unit,PointExecuteAPI.filled (FullMainFrame.base total i) c d)) pointEq) pointRun
  have expression : evalExpr SynergyC.Header.layout FullMainPrefix.service 128
      (PointExecuteAPI.buffers (FullMainFrame.base total i)) MainInputPointComposition.expression=
      some (.unit,PointExecuteAPI.filled (FullMainFrame.base total i) c d) := by
    rw [MainInputPointComposition.eval_actual_inputs]
    exact called
  have buffers : ScopedIO.WorldSource.Run SynergyC.Header.layout FullMainPrefix.service service platform
      (.declare PointExecuteAPI.declarations) ⟨FullMainFrame.base total i,stream⟩
      (.continuing ⟨PointExecuteAPI.buffers (FullMainFrame.base total i),stream⟩) :=
    Loops.StmtRun.declare ⟨PointExecuteAPI.buffers_from_actual_declaration _ _,rfl⟩
  have point : ScopedIO.WorldSource.Run SynergyC.Header.layout FullMainPrefix.service service platform
      (.eval MainInputPointComposition.expression)
      ⟨PointExecuteAPI.buffers (FullMainFrame.base total i),stream⟩
      (.continuing ⟨PointExecuteAPI.filled (FullMainFrame.base total i) c d,stream⟩) :=
    Loops.StmtRun.evaluate (.pure expression)
  have all := EmitUSource.world_seq_append first
    (Loops.SeqRun.next buffers (Loops.SeqRun.next point (Loops.SeqRun.nil _)))
  rw [←MainInputPointComposition.actual_loop_prefix] at all
  exact all

theorem actual_budget (service : ScopedIO.WorldIO.Call)
    (platform : ScopedIO.WorldIO.Platform) (stream : ScopedIO.Stream)
    (total c d : ProofBox) (i : Nat)
    (execution : MainBudgetExecute.run total i c d=some
      (.continuing (MainBudgetExecute.afterBudget total i c d))) :
    Loops.SeqRun (ScopedIO.WorldSource.Eval SynergyC.Header.layout FullMainPrefix.service service platform)
      (ScopedIO.WorldSource.Declare SynergyC.Header.layout FullMainPrefix.service)
      truth ScopedIO.WorldSource.Scope MainBudgetExecute.statements
      ⟨MainBudgetExecute.before total i c d,stream⟩
      (.continuing ⟨MainBudgetExecute.afterBudget total i c d,stream⟩) := by
  have eq : MainBudgetExecute.run total i c d=ArraySourceExecute.statements
      SynergyC.Header.layout FullMainPrefix.service 128 2048 MainBudgetExecute.statements
      (MainBudgetExecute.before total i c d) := by
    unfold MainBudgetExecute.run
    rfl
  have actual := Eq.mp (congrArg (fun r=>r=some
    (.continuing (MainBudgetExecute.afterBudget total i c d))) eq) execution
  exact (ScopedIO.WorldLift.pure_sound SynergyC.Header.layout FullMainPrefix.service
    service platform stream 128 2048).2.1 _ _ _ actual

#print axioms actual_point_prefix
#print axioms actual_budget
end SynergyHeightC.MainWorldPrefix
