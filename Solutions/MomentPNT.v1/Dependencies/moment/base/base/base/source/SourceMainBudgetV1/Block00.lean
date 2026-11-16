import SourceMainBudgetV1.Cell0000
import SourceHeightEdgesV1.Edge0000
import SourceMainBudgetV1.Cell0001
import SourceHeightEdgesV1.Edge0001
import SourceMainBudgetV1.Cell0002
import SourceHeightEdgesV1.Edge0002
import SourceMainBudgetV1.Cell0003
import SourceHeightEdgesV1.Edge0003
import SourceMainBudgetV1.Cell0004
import SourceHeightEdgesV1.Edge0004
import SourceMainBudgetV1.Cell0005
import SourceHeightEdgesV1.Edge0005
import SourceMainBudgetV1.Cell0006
import SourceHeightEdgesV1.Edge0006
import SourceMainBudgetV1.Cell0007
import SourceHeightEdgesV1.Edge0007
import SourceMainBudgetV1.Cell0008
import SourceHeightEdgesV1.Edge0008
import SourceMainBudgetV1.Cell0009
import SourceHeightEdgesV1.Edge0009
import SourceMainBudgetV1.Cell0010
import SourceHeightEdgesV1.Edge0010
import SourceMainBudgetV1.Cell0011
import SourceHeightEdgesV1.Edge0011
import SourceMainBudgetV1.Cell0012
import SourceHeightEdgesV1.Edge0012
import SourceMainBudgetV1.Cell0013
import SourceHeightEdgesV1.Edge0013
import SourceMainBudgetV1.Cell0014
import SourceHeightEdgesV1.Edge0014
import SourceMainBudgetV1.Cell0015
import SourceHeightEdgesV1.Edge0015
import SourceMainBudgetV1.Cell0016
import SourceHeightEdgesV1.Edge0016
import SourceMainBudgetV1.Cell0017
import SourceHeightEdgesV1.Edge0017
import SourceMainBudgetV1.Cell0018
import SourceHeightEdgesV1.Edge0018
import SourceMainBudgetV1.Cell0019
import SourceHeightEdgesV1.Edge0019
import SourceMainBudgetV1.Cell0020
import SourceHeightEdgesV1.Edge0020
import SourceMainBudgetV1.Cell0021
import SourceHeightEdgesV1.Edge0021
import SourceMainBudgetV1.Cell0022
import SourceHeightEdgesV1.Edge0022
import SourceMainBudgetV1.Cell0023
import SourceHeightEdgesV1.Edge0023
import SourceMainBudgetV1.Cell0024
import SourceHeightEdgesV1.Edge0024
import SourceMainBudgetV1.Cell0025
import SourceHeightEdgesV1.Edge0025
import SourceMainBudgetV1.Cell0026
import SourceHeightEdgesV1.Edge0026
import SourceMainBudgetV1.Cell0027
import SourceHeightEdgesV1.Edge0027
import SourceMainBudgetV1.Cell0028
import SourceHeightEdgesV1.Edge0028
import SourceMainBudgetV1.Cell0029
import SourceHeightEdgesV1.Edge0029
import SourceMainBudgetV1.Cell0030
import SourceHeightEdgesV1.Edge0030
import SourceMainBudgetV1.Cell0031
import SourceHeightEdgesV1.Edge0031
import SourceMainBudgetV1.Data
import Mathlib.Tactic.IntervalCases
namespace SourceMainBudgetV1.Block00
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem all (i : Nat) (lower : 0 ≤ i) (upper : i < 32) :
 SourceMainBudgetV1.Data.Cell i := by
 interval_cases i
 · exact SourceMainBudgetV1.Data.pack (i:=0) (input:=SourceMainFramesV1.Point0000.input) (pair:=SourceMainFramesV1.Point0000.outputs) SourceHeightEdgesV1.Edge0000.left_defined SourceMainFramesV1.Point0000.input_defined SourceMainFramesV1.Point0000.outputs_defined SourceMainBudgetV1.Cell0000.execution SourceMainBudgetV1.Cell0000.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=1) (input:=SourceMainFramesV1.Point0001.input) (pair:=SourceMainFramesV1.Point0001.outputs) SourceHeightEdgesV1.Edge0001.left_defined SourceMainFramesV1.Point0001.input_defined SourceMainFramesV1.Point0001.outputs_defined SourceMainBudgetV1.Cell0001.execution SourceMainBudgetV1.Cell0001.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=2) (input:=SourceMainFramesV1.Point0002.input) (pair:=SourceMainFramesV1.Point0002.outputs) SourceHeightEdgesV1.Edge0002.left_defined SourceMainFramesV1.Point0002.input_defined SourceMainFramesV1.Point0002.outputs_defined SourceMainBudgetV1.Cell0002.execution SourceMainBudgetV1.Cell0002.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=3) (input:=SourceMainFramesV1.Point0003.input) (pair:=SourceMainFramesV1.Point0003.outputs) SourceHeightEdgesV1.Edge0003.left_defined SourceMainFramesV1.Point0003.input_defined SourceMainFramesV1.Point0003.outputs_defined SourceMainBudgetV1.Cell0003.execution SourceMainBudgetV1.Cell0003.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=4) (input:=SourceMainFramesV1.Point0004.input) (pair:=SourceMainFramesV1.Point0004.outputs) SourceHeightEdgesV1.Edge0004.left_defined SourceMainFramesV1.Point0004.input_defined SourceMainFramesV1.Point0004.outputs_defined SourceMainBudgetV1.Cell0004.execution SourceMainBudgetV1.Cell0004.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=5) (input:=SourceMainFramesV1.Point0005.input) (pair:=SourceMainFramesV1.Point0005.outputs) SourceHeightEdgesV1.Edge0005.left_defined SourceMainFramesV1.Point0005.input_defined SourceMainFramesV1.Point0005.outputs_defined SourceMainBudgetV1.Cell0005.execution SourceMainBudgetV1.Cell0005.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=6) (input:=SourceMainFramesV1.Point0006.input) (pair:=SourceMainFramesV1.Point0006.outputs) SourceHeightEdgesV1.Edge0006.left_defined SourceMainFramesV1.Point0006.input_defined SourceMainFramesV1.Point0006.outputs_defined SourceMainBudgetV1.Cell0006.execution SourceMainBudgetV1.Cell0006.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=7) (input:=SourceMainFramesV1.Point0007.input) (pair:=SourceMainFramesV1.Point0007.outputs) SourceHeightEdgesV1.Edge0007.left_defined SourceMainFramesV1.Point0007.input_defined SourceMainFramesV1.Point0007.outputs_defined SourceMainBudgetV1.Cell0007.execution SourceMainBudgetV1.Cell0007.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=8) (input:=SourceMainFramesV1.Point0008.input) (pair:=SourceMainFramesV1.Point0008.outputs) SourceHeightEdgesV1.Edge0008.left_defined SourceMainFramesV1.Point0008.input_defined SourceMainFramesV1.Point0008.outputs_defined SourceMainBudgetV1.Cell0008.execution SourceMainBudgetV1.Cell0008.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=9) (input:=SourceMainFramesV1.Point0009.input) (pair:=SourceMainFramesV1.Point0009.outputs) SourceHeightEdgesV1.Edge0009.left_defined SourceMainFramesV1.Point0009.input_defined SourceMainFramesV1.Point0009.outputs_defined SourceMainBudgetV1.Cell0009.execution SourceMainBudgetV1.Cell0009.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=10) (input:=SourceMainFramesV1.Point0010.input) (pair:=SourceMainFramesV1.Point0010.outputs) SourceHeightEdgesV1.Edge0010.left_defined SourceMainFramesV1.Point0010.input_defined SourceMainFramesV1.Point0010.outputs_defined SourceMainBudgetV1.Cell0010.execution SourceMainBudgetV1.Cell0010.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=11) (input:=SourceMainFramesV1.Point0011.input) (pair:=SourceMainFramesV1.Point0011.outputs) SourceHeightEdgesV1.Edge0011.left_defined SourceMainFramesV1.Point0011.input_defined SourceMainFramesV1.Point0011.outputs_defined SourceMainBudgetV1.Cell0011.execution SourceMainBudgetV1.Cell0011.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=12) (input:=SourceMainFramesV1.Point0012.input) (pair:=SourceMainFramesV1.Point0012.outputs) SourceHeightEdgesV1.Edge0012.left_defined SourceMainFramesV1.Point0012.input_defined SourceMainFramesV1.Point0012.outputs_defined SourceMainBudgetV1.Cell0012.execution SourceMainBudgetV1.Cell0012.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=13) (input:=SourceMainFramesV1.Point0013.input) (pair:=SourceMainFramesV1.Point0013.outputs) SourceHeightEdgesV1.Edge0013.left_defined SourceMainFramesV1.Point0013.input_defined SourceMainFramesV1.Point0013.outputs_defined SourceMainBudgetV1.Cell0013.execution SourceMainBudgetV1.Cell0013.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=14) (input:=SourceMainFramesV1.Point0014.input) (pair:=SourceMainFramesV1.Point0014.outputs) SourceHeightEdgesV1.Edge0014.left_defined SourceMainFramesV1.Point0014.input_defined SourceMainFramesV1.Point0014.outputs_defined SourceMainBudgetV1.Cell0014.execution SourceMainBudgetV1.Cell0014.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=15) (input:=SourceMainFramesV1.Point0015.input) (pair:=SourceMainFramesV1.Point0015.outputs) SourceHeightEdgesV1.Edge0015.left_defined SourceMainFramesV1.Point0015.input_defined SourceMainFramesV1.Point0015.outputs_defined SourceMainBudgetV1.Cell0015.execution SourceMainBudgetV1.Cell0015.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=16) (input:=SourceMainFramesV1.Point0016.input) (pair:=SourceMainFramesV1.Point0016.outputs) SourceHeightEdgesV1.Edge0016.left_defined SourceMainFramesV1.Point0016.input_defined SourceMainFramesV1.Point0016.outputs_defined SourceMainBudgetV1.Cell0016.execution SourceMainBudgetV1.Cell0016.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=17) (input:=SourceMainFramesV1.Point0017.input) (pair:=SourceMainFramesV1.Point0017.outputs) SourceHeightEdgesV1.Edge0017.left_defined SourceMainFramesV1.Point0017.input_defined SourceMainFramesV1.Point0017.outputs_defined SourceMainBudgetV1.Cell0017.execution SourceMainBudgetV1.Cell0017.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=18) (input:=SourceMainFramesV1.Point0018.input) (pair:=SourceMainFramesV1.Point0018.outputs) SourceHeightEdgesV1.Edge0018.left_defined SourceMainFramesV1.Point0018.input_defined SourceMainFramesV1.Point0018.outputs_defined SourceMainBudgetV1.Cell0018.execution SourceMainBudgetV1.Cell0018.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=19) (input:=SourceMainFramesV1.Point0019.input) (pair:=SourceMainFramesV1.Point0019.outputs) SourceHeightEdgesV1.Edge0019.left_defined SourceMainFramesV1.Point0019.input_defined SourceMainFramesV1.Point0019.outputs_defined SourceMainBudgetV1.Cell0019.execution SourceMainBudgetV1.Cell0019.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=20) (input:=SourceMainFramesV1.Point0020.input) (pair:=SourceMainFramesV1.Point0020.outputs) SourceHeightEdgesV1.Edge0020.left_defined SourceMainFramesV1.Point0020.input_defined SourceMainFramesV1.Point0020.outputs_defined SourceMainBudgetV1.Cell0020.execution SourceMainBudgetV1.Cell0020.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=21) (input:=SourceMainFramesV1.Point0021.input) (pair:=SourceMainFramesV1.Point0021.outputs) SourceHeightEdgesV1.Edge0021.left_defined SourceMainFramesV1.Point0021.input_defined SourceMainFramesV1.Point0021.outputs_defined SourceMainBudgetV1.Cell0021.execution SourceMainBudgetV1.Cell0021.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=22) (input:=SourceMainFramesV1.Point0022.input) (pair:=SourceMainFramesV1.Point0022.outputs) SourceHeightEdgesV1.Edge0022.left_defined SourceMainFramesV1.Point0022.input_defined SourceMainFramesV1.Point0022.outputs_defined SourceMainBudgetV1.Cell0022.execution SourceMainBudgetV1.Cell0022.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=23) (input:=SourceMainFramesV1.Point0023.input) (pair:=SourceMainFramesV1.Point0023.outputs) SourceHeightEdgesV1.Edge0023.left_defined SourceMainFramesV1.Point0023.input_defined SourceMainFramesV1.Point0023.outputs_defined SourceMainBudgetV1.Cell0023.execution SourceMainBudgetV1.Cell0023.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=24) (input:=SourceMainFramesV1.Point0024.input) (pair:=SourceMainFramesV1.Point0024.outputs) SourceHeightEdgesV1.Edge0024.left_defined SourceMainFramesV1.Point0024.input_defined SourceMainFramesV1.Point0024.outputs_defined SourceMainBudgetV1.Cell0024.execution SourceMainBudgetV1.Cell0024.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=25) (input:=SourceMainFramesV1.Point0025.input) (pair:=SourceMainFramesV1.Point0025.outputs) SourceHeightEdgesV1.Edge0025.left_defined SourceMainFramesV1.Point0025.input_defined SourceMainFramesV1.Point0025.outputs_defined SourceMainBudgetV1.Cell0025.execution SourceMainBudgetV1.Cell0025.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=26) (input:=SourceMainFramesV1.Point0026.input) (pair:=SourceMainFramesV1.Point0026.outputs) SourceHeightEdgesV1.Edge0026.left_defined SourceMainFramesV1.Point0026.input_defined SourceMainFramesV1.Point0026.outputs_defined SourceMainBudgetV1.Cell0026.execution SourceMainBudgetV1.Cell0026.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=27) (input:=SourceMainFramesV1.Point0027.input) (pair:=SourceMainFramesV1.Point0027.outputs) SourceHeightEdgesV1.Edge0027.left_defined SourceMainFramesV1.Point0027.input_defined SourceMainFramesV1.Point0027.outputs_defined SourceMainBudgetV1.Cell0027.execution SourceMainBudgetV1.Cell0027.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=28) (input:=SourceMainFramesV1.Point0028.input) (pair:=SourceMainFramesV1.Point0028.outputs) SourceHeightEdgesV1.Edge0028.left_defined SourceMainFramesV1.Point0028.input_defined SourceMainFramesV1.Point0028.outputs_defined SourceMainBudgetV1.Cell0028.execution SourceMainBudgetV1.Cell0028.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=29) (input:=SourceMainFramesV1.Point0029.input) (pair:=SourceMainFramesV1.Point0029.outputs) SourceHeightEdgesV1.Edge0029.left_defined SourceMainFramesV1.Point0029.input_defined SourceMainFramesV1.Point0029.outputs_defined SourceMainBudgetV1.Cell0029.execution SourceMainBudgetV1.Cell0029.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=30) (input:=SourceMainFramesV1.Point0030.input) (pair:=SourceMainFramesV1.Point0030.outputs) SourceHeightEdgesV1.Edge0030.left_defined SourceMainFramesV1.Point0030.input_defined SourceMainFramesV1.Point0030.outputs_defined SourceMainBudgetV1.Cell0030.execution SourceMainBudgetV1.Cell0030.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=31) (input:=SourceMainFramesV1.Point0031.input) (pair:=SourceMainFramesV1.Point0031.outputs) SourceHeightEdgesV1.Edge0031.left_defined SourceMainFramesV1.Point0031.input_defined SourceMainFramesV1.Point0031.outputs_defined SourceMainBudgetV1.Cell0031.execution SourceMainBudgetV1.Cell0031.next_total
end SourceMainBudgetV1.Block00
open Lean Elab
run_elab do
 let n := `SourceMainBudgetV1.Block00.all
 let env ← getEnv
 let some ci := env.find? n | throwError "missing actual source cell block"
 let ax ← Lean.collectAxioms n
 logInfo m!"BUDGET_BLOCK_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
