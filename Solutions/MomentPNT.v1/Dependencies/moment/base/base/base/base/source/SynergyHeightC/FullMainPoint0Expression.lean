/- Bind the source call expression to the actual caller's right/c/D locals.
This module does not assume a source-run result or a completed loop. -/
import SynergyHeightC.FullMainPoint0
namespace SynergyHeightC.FullMainPoint0Expression
open ScopedC ScopedC.Syntax ScopedC.Machine ScopedNumerical
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def expression : Expr := .call (.var "pointHeight")
  [.var "right",.unary "&" (.var "c"),.unary "&" (.var "D")]

theorem actual_statement : PointExecuteAPI.loopStatements[3]?=some (.eval expression) := by rfl

def baseOfRight (right : ProofBox) : State :=
  allocate FullMainEdge.afterLeft "I" "right"
    (some (SynergyC.SourceIntervalMath.represented right))

theorem eval_symbolic_right_inputs (call : Call) (right : ProofBox) :
    evalExpr SynergyC.Header.layout call 128 (PointExecuteAPI.buffers (baseOfRight right)) expression =
      call "pointHeight" (PointExecuteAPI.args (baseOfRight right) right)
        (PointExecuteAPI.buffers (baseOfRight right)) := by rfl

theorem eval_actual_inputs (call : Call) :
    evalExpr SynergyC.Header.layout call 128 (PointExecuteAPI.buffers FullMainEdge.afterRight) expression =
      call "pointHeight" (PointExecuteAPI.args FullMainEdge.afterRight FullMainEdge.right)
        (PointExecuteAPI.buffers FullMainEdge.afterRight) :=
  eval_symbolic_right_inputs call FullMainEdge.right

/-- The closed numerical run is converted into the actual main statement
only after the exact source expression has computed these SAME arguments. -/
theorem statement_of_run {after : State}
    (h : FullContractPointExecute.run FullMainEdge.afterRight FullMainEdge.right=some (.unit,after)) :
    ArraySourceCalls.Run SynergyC.Header.layout FullMainPrefix.service (.eval expression)
      (PointExecuteAPI.buffers FullMainEdge.afterRight) (.continuing after) := by
  have run_eq : FullContractPointExecute.run FullMainEdge.afterRight FullMainEdge.right=
      FullMainPrefix.service "pointHeight" (PointExecuteAPI.args FullMainEdge.afterRight FullMainEdge.right)
        (PointExecuteAPI.buffers FullMainEdge.afterRight) := by
    unfold FullContractPointExecute.run; rfl
  have exec := Eq.mp (congrArg (fun result=>result=some (.unit,after)) run_eq) h
  apply Loops.StmtRun.evaluate
  refine ⟨128,?_⟩
  rw [eval_actual_inputs]
  exact exec

#print axioms actual_statement
#print axioms eval_actual_inputs
#print axioms statement_of_run
end SynergyHeightC.FullMainPoint0Expression
