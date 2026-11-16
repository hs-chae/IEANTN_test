/- Actual unsigned main-loop guard, including the final i=768 stop. -/
import SynergyHeightC.MainWorldIteration
namespace SynergyHeightC.MainWorldGuard
open ScopedC ScopedC.Syntax ScopedC.Machine ScopedNumerical
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 100000

def guard : Expr := .binary "<" (.var "i") (.var "cells")

theorem read_i (call : Machine.Call) (total : ProofBox) (i : Nat) :
    evalExpr SynergyC.Header.layout call 1 (FullMainEdges.loopState total i) (.var "i")=
      some (FullMainPrefix.unsigned32 i,FullMainEdges.loopState total i) := by
  simp [evalExpr,Machine.getVar,FullMainEdges.loopState,Machine.allocate,Machine.read,
    Machine.nested,Machine.initialized,FullMainPrefix.unsigned32]

theorem read_cells (call : Machine.Call) (total : ProofBox) (i : Nat) :
    evalExpr SynergyC.Header.layout call 1 (FullMainEdges.loopState total i) (.var "cells")=
      some (FullMainPrefix.unsigned32 768,FullMainEdges.loopState total i) := by
  simp [evalExpr,Machine.getVar,FullMainEdges.loopState,FullMainPrefix.afterSpan,
    FullMainPrefix.afterHeight,FullMainPrefix.afterCells,Machine.allocate,Machine.read,
    Machine.nested,Machine.initialized,FullMainPrefix.unsigned32,List.lookup]

theorem actual_guard (call : Machine.Call) (total : ProofBox) (i : Nat) (bound : i<2^32) :
    evalExpr SynergyC.Header.layout call 2 (FullMainEdges.loopState total i) guard=
      some (Machine.boolean SynergyC.Header.layout (decide (i<768)),
        FullMainEdges.loopState total i) :=
  ExpressionTemplates.binary SynergyC.Header.layout call
    (by decide) (by decide) (by decide) (by decide)
    (read_i call total i) (read_cells call total i)
    (PoolCalls.binary_lt (FullMainEdges.loopState total i) i 768 bound (by decide))

theorem world_guard (service : ScopedIO.WorldIO.Call) (platform : ScopedIO.WorldIO.Platform)
    (stream : ScopedIO.Stream) (total : ProofBox) (i : Nat) (bound : i<2^32) :
    ScopedIO.WorldSource.Eval SynergyC.Header.layout FullMainPrefix.service service platform
      guard ⟨FullMainEdges.loopState total i,stream⟩ ⟨FullMainEdges.loopState total i,stream⟩
      (Machine.boolean SynergyC.Header.layout (decide (i<768))) :=
  .pure (actual_guard FullMainPrefix.service total i bound)

theorem actual_main_loop : PointExecuteAPI.mainStatements[6]?=
    some (.whileLoop guard (.sequence PointExecuteAPI.loopStatements)) := by rfl

#print axioms actual_guard
#print axioms world_guard
end SynergyHeightC.MainWorldGuard
