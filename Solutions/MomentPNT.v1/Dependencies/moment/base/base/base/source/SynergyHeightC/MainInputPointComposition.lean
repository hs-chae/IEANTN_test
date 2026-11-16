/- Actual main input declarations and the point call use one continuous
source trace. Exact source outputs, pointer reads and mathematical meanings
are coupled; completed finite providers must discharge both execution inputs. -/
import SynergyHeightC.FullMainEdges
import SynergyHeightC.FullMainPoint0Flow
import SynergyHeightC.FramedPointReplayAPI
namespace SynergyHeightC.MainInputPointComposition
open ScopedC ScopedC.Syntax ScopedC.Machine ScopedNumerical
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def input (i : Nat) : ProofBox := (SynergyAnalytic.HeightPoint.logCell (i+1)).getD ⟨0,0⟩
def expression : Expr := .call (.var "pointHeight")
  [.var "right",.unary "&" (.var "c"),.unary "&" (.var "D")]

theorem actual_loop_prefix : PointExecuteAPI.loopStatements.take 4=
    FullMainEdge.statements++[.declare PointExecuteAPI.declarations,.eval expression] := by rfl

def baseWithRight (total : ProofBox) (i : Nat) (right : ProofBox) : State :=
  allocate (FullMainFrame.throughLeft total i) "I" "right"
    (some (SynergyC.SourceIntervalMath.represented right))

theorem eval_symbolic_inputs (call : Machine.Call) (total : ProofBox) (i : Nat) (right : ProofBox) :
    evalExpr SynergyC.Header.layout call 128 (PointExecuteAPI.buffers (baseWithRight total i right)) expression=
      call "pointHeight" (PointExecuteAPI.args (baseWithRight total i right) right)
        (PointExecuteAPI.buffers (baseWithRight total i right)) := by rfl

theorem eval_actual_inputs (call : Machine.Call) (total : ProofBox) (i : Nat) :
    evalExpr SynergyC.Header.layout call 128 (PointExecuteAPI.buffers (FullMainFrame.base total i)) expression=
      call "pointHeight" (PointExecuteAPI.args (FullMainFrame.base total i) (input i))
        (PointExecuteAPI.buffers (FullMainFrame.base total i)) :=
  eval_symbolic_inputs call total i (input i)

theorem statement_of_execution {total c d : ProofBox} {i : Nat}
    (execution : FullContractPointExecute.run (FullMainFrame.base total i) (input i)=
      some (.unit,PointExecuteAPI.filled (FullMainFrame.base total i) c d)) :
    ArraySourceCalls.Run SynergyC.Header.layout FullMainPrefix.service (.eval expression)
      (PointExecuteAPI.buffers (FullMainFrame.base total i))
      (.continuing (PointExecuteAPI.filled (FullMainFrame.base total i) c d)) := by
  have run_eq : FullContractPointExecute.run (FullMainFrame.base total i) (input i)=
      FullMainPrefix.service "pointHeight" (PointExecuteAPI.args (FullMainFrame.base total i) (input i))
        (PointExecuteAPI.buffers (FullMainFrame.base total i)) := by
    unfold FullContractPointExecute.run; rfl
  have exec := Eq.mp (congrArg (fun result=>result=some
    (.unit,PointExecuteAPI.filled (FullMainFrame.base total i) c d)) run_eq) execution
  apply Loops.StmtRun.evaluate
  refine ⟨128,?_⟩
  rw [eval_actual_inputs]
  exact exec

/-- Source pointEdge declarations supply the actual pointHeight input in
this SAME main frame. No synthetic bare-cache call is substituted. -/
theorem source_prefix {i : Nat} (edges : FullMainEdges.ExactEdges i) (total c d : ProofBox)
    (execution : FullContractPointExecute.run (FullMainFrame.base total i) (input i)=
      some (.unit,PointExecuteAPI.filled (FullMainFrame.base total i) c d)) :
    Loops.SeqRun (ArraySourceCalls.Eval SynergyC.Header.layout FullMainPrefix.service)
      (ArraySourceCalls.Declare SynergyC.Header.layout FullMainPrefix.service) truth ArraySourceCalls.Scope
      (PointExecuteAPI.loopStatements.take 4) (FullMainEdges.loopState total i)
      (.continuing (PointExecuteAPI.filled (FullMainFrame.base total i) c d)) := by
  have first := FullMainEdges.actual_source_edges edges total
  have buffers : ArraySourceCalls.Run SynergyC.Header.layout FullMainPrefix.service
      (.declare PointExecuteAPI.declarations) (FullMainFrame.base total i)
      (.continuing (PointExecuteAPI.buffers (FullMainFrame.base total i))) :=
    Loops.StmtRun.declare (PointExecuteAPI.buffers_from_actual_declaration _ _)
  have call := statement_of_execution execution
  have tail := Loops.SeqRun.next buffers (Loops.SeqRun.next call (Loops.SeqRun.nil _))
  have all := FullMainPoint0Flow.seq_append first tail
  rw [←actual_loop_prefix] at all
  exact all

/-- Exact same source prefix and actual pointer records, with their proved
mathematical intervals. The finite all-cell facts remove these provider hypotheses. -/
theorem source_prefix_enclosures {i : Nat} (edges : FullMainEdges.ExactEdges i) (total c d : ProofBox)
    (execution : FullContractPointExecute.run (FullMainFrame.base total i) (input i)=
      some (.unit,PointExecuteAPI.filled (FullMainFrame.base total i) c d))
    (model : PointExecuteAPI.modelOutputs (input i)=some (c,d)) {x : ℝ}
    (hx : SynergyBasis.RealBox.Contains 128 (input i) x) :
    Loops.SeqRun (ArraySourceCalls.Eval SynergyC.Header.layout FullMainPrefix.service)
      (ArraySourceCalls.Declare SynergyC.Header.layout FullMainPrefix.service) truth ArraySourceCalls.Scope
      (PointExecuteAPI.loopStatements.take 4) (FullMainEdges.loopState total i)
      (.continuing (PointExecuteAPI.filled (FullMainFrame.base total i) c d)) ∧
    Machine.read SynergyC.Header.layout (PointExecuteAPI.filled (FullMainFrame.base total i) c d) ⟨21,0,[]⟩=
      some (SynergyC.SourceIntervalMath.represented c) ∧
    Machine.read SynergyC.Header.layout (PointExecuteAPI.filled (FullMainFrame.base total i) c d) ⟨22,0,[]⟩=
      some (SynergyC.SourceIntervalMath.represented d) ∧
    SynergyBasis.RealBox.Contains 128 c (SynergyAnalytic.HeightPoint.r184 x) ∧
    SynergyBasis.RealBox.Contains 128 d (SynergyAnalytic.HeightPoint.r186 x) := by
  obtain ⟨mc,md⟩ := PointExecuteAPI.model_output_enclosures model hx
  exact ⟨source_prefix edges total c d execution,
    FramedPointReplayAPI.read_filled_c _ c d,FramedPointReplayAPI.read_filled_d _ c d,mc,md⟩

#print axioms eval_actual_inputs
#print axioms statement_of_execution
#print axioms source_prefix
#print axioms source_prefix_enclosures
end SynergyHeightC.MainInputPointComposition
