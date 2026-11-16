import SourceMainBudgetV1.Block00
import SourceMainBudgetV1.Block01
import SourceMainBudgetV1.Block02
import SourceMainBudgetV1.Block03
import SourceMainBudgetV1.Block04
import SourceMainBudgetV1.Block05
import SourceMainBudgetV1.Block06
import SourceMainBudgetV1.Block07
import SourceMainBudgetV1.Block08
import SourceMainBudgetV1.Block09
import SourceMainBudgetV1.Block10
import SourceMainBudgetV1.Block11
import SourceMainBudgetV1.Block12
import SourceMainBudgetV1.Block13
import SourceMainBudgetV1.Block14
import SourceMainBudgetV1.Block15
import SourceMainBudgetV1.Block16
import SourceMainBudgetV1.Block17
import SourceMainBudgetV1.Block18
import SourceMainBudgetV1.Block19
import SourceMainBudgetV1.Block20
import SourceMainBudgetV1.Block21
import SourceMainBudgetV1.Block22
import SourceMainBudgetV1.Block23
import Lean.Elab.Tactic.Omega
namespace SourceMainBudgetV1.All
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem cells (i : Nat) (hi : i < 768) : SourceMainBudgetV1.Data.Cell i := by
 let j:=i/32
 have hj : j < 24 := by dsimp [j];omega
 have lower : 32*j ≤ i := by dsimp [j];omega
 have upper : i < 32*(j+1) := by dsimp [j];omega
 interval_cases j
 · exact SourceMainBudgetV1.Block00.all i (by omega) (by omega)
 · exact SourceMainBudgetV1.Block01.all i (by omega) (by omega)
 · exact SourceMainBudgetV1.Block02.all i (by omega) (by omega)
 · exact SourceMainBudgetV1.Block03.all i (by omega) (by omega)
 · exact SourceMainBudgetV1.Block04.all i (by omega) (by omega)
 · exact SourceMainBudgetV1.Block05.all i (by omega) (by omega)
 · exact SourceMainBudgetV1.Block06.all i (by omega) (by omega)
 · exact SourceMainBudgetV1.Block07.all i (by omega) (by omega)
 · exact SourceMainBudgetV1.Block08.all i (by omega) (by omega)
 · exact SourceMainBudgetV1.Block09.all i (by omega) (by omega)
 · exact SourceMainBudgetV1.Block10.all i (by omega) (by omega)
 · exact SourceMainBudgetV1.Block11.all i (by omega) (by omega)
 · exact SourceMainBudgetV1.Block12.all i (by omega) (by omega)
 · exact SourceMainBudgetV1.Block13.all i (by omega) (by omega)
 · exact SourceMainBudgetV1.Block14.all i (by omega) (by omega)
 · exact SourceMainBudgetV1.Block15.all i (by omega) (by omega)
 · exact SourceMainBudgetV1.Block16.all i (by omega) (by omega)
 · exact SourceMainBudgetV1.Block17.all i (by omega) (by omega)
 · exact SourceMainBudgetV1.Block18.all i (by omega) (by omega)
 · exact SourceMainBudgetV1.Block19.all i (by omega) (by omega)
 · exact SourceMainBudgetV1.Block20.all i (by omega) (by omega)
 · exact SourceMainBudgetV1.Block21.all i (by omega) (by omega)
 · exact SourceMainBudgetV1.Block22.all i (by omega) (by omega)
 · exact SourceMainBudgetV1.Block23.all i (by omega) (by omega)
end SourceMainBudgetV1.All
open Lean Elab
run_elab do
 let n := `SourceMainBudgetV1.All.cells
 let env ← getEnv
 let some ci := env.find? n | throwError "missing all768 actual source cell family"
 let ax ← Lean.collectAxioms n
 logInfo m!"ALL_SOURCE_BUDGET_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
