import SourceMainBudgetV1.Cell0032
import SourceHeightEdgesV1.Edge0032
import SourceMainBudgetV1.Cell0033
import SourceHeightEdgesV1.Edge0033
import SourceMainBudgetV1.Cell0034
import SourceHeightEdgesV1.Edge0034
import SourceMainBudgetV1.Cell0035
import SourceHeightEdgesV1.Edge0035
import SourceMainBudgetV1.Cell0036
import SourceHeightEdgesV1.Edge0036
import SourceMainBudgetV1.Cell0037
import SourceHeightEdgesV1.Edge0037
import SourceMainBudgetV1.Cell0038
import SourceHeightEdgesV1.Edge0038
import SourceMainBudgetV1.Cell0039
import SourceHeightEdgesV1.Edge0039
import SourceMainBudgetV1.Cell0040
import SourceHeightEdgesV1.Edge0040
import SourceMainBudgetV1.Cell0041
import SourceHeightEdgesV1.Edge0041
import SourceMainBudgetV1.Cell0042
import SourceHeightEdgesV1.Edge0042
import SourceMainBudgetV1.Cell0043
import SourceHeightEdgesV1.Edge0043
import SourceMainBudgetV1.Cell0044
import SourceHeightEdgesV1.Edge0044
import SourceMainBudgetV1.Cell0045
import SourceHeightEdgesV1.Edge0045
import SourceMainBudgetV1.Cell0046
import SourceHeightEdgesV1.Edge0046
import SourceMainBudgetV1.Cell0047
import SourceHeightEdgesV1.Edge0047
import SourceMainBudgetV1.Cell0048
import SourceHeightEdgesV1.Edge0048
import SourceMainBudgetV1.Cell0049
import SourceHeightEdgesV1.Edge0049
import SourceMainBudgetV1.Cell0050
import SourceHeightEdgesV1.Edge0050
import SourceMainBudgetV1.Cell0051
import SourceHeightEdgesV1.Edge0051
import SourceMainBudgetV1.Cell0052
import SourceHeightEdgesV1.Edge0052
import SourceMainBudgetV1.Cell0053
import SourceHeightEdgesV1.Edge0053
import SourceMainBudgetV1.Cell0054
import SourceHeightEdgesV1.Edge0054
import SourceMainBudgetV1.Cell0055
import SourceHeightEdgesV1.Edge0055
import SourceMainBudgetV1.Cell0056
import SourceHeightEdgesV1.Edge0056
import SourceMainBudgetV1.Cell0057
import SourceHeightEdgesV1.Edge0057
import SourceMainBudgetV1.Cell0058
import SourceHeightEdgesV1.Edge0058
import SourceMainBudgetV1.Cell0059
import SourceHeightEdgesV1.Edge0059
import SourceMainBudgetV1.Cell0060
import SourceHeightEdgesV1.Edge0060
import SourceMainBudgetV1.Cell0061
import SourceHeightEdgesV1.Edge0061
import SourceMainBudgetV1.Cell0062
import SourceHeightEdgesV1.Edge0062
import SourceMainBudgetV1.Cell0063
import SourceHeightEdgesV1.Edge0063
import SourceMainBudgetV1.Data
import Mathlib.Tactic.IntervalCases
namespace SourceMainBudgetV1.Block01
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem all (i : Nat) (lower : 32 ≤ i) (upper : i < 64) :
 SourceMainBudgetV1.Data.Cell i := by
 interval_cases i
 · exact SourceMainBudgetV1.Data.pack (i:=32) (input:=SourceMainFramesV1.Point0032.input) (pair:=SourceMainFramesV1.Point0032.outputs) SourceHeightEdgesV1.Edge0032.left_defined SourceMainFramesV1.Point0032.input_defined SourceMainFramesV1.Point0032.outputs_defined SourceMainBudgetV1.Cell0032.execution SourceMainBudgetV1.Cell0032.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=33) (input:=SourceMainFramesV1.Point0033.input) (pair:=SourceMainFramesV1.Point0033.outputs) SourceHeightEdgesV1.Edge0033.left_defined SourceMainFramesV1.Point0033.input_defined SourceMainFramesV1.Point0033.outputs_defined SourceMainBudgetV1.Cell0033.execution SourceMainBudgetV1.Cell0033.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=34) (input:=SourceMainFramesV1.Point0034.input) (pair:=SourceMainFramesV1.Point0034.outputs) SourceHeightEdgesV1.Edge0034.left_defined SourceMainFramesV1.Point0034.input_defined SourceMainFramesV1.Point0034.outputs_defined SourceMainBudgetV1.Cell0034.execution SourceMainBudgetV1.Cell0034.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=35) (input:=SourceMainFramesV1.Point0035.input) (pair:=SourceMainFramesV1.Point0035.outputs) SourceHeightEdgesV1.Edge0035.left_defined SourceMainFramesV1.Point0035.input_defined SourceMainFramesV1.Point0035.outputs_defined SourceMainBudgetV1.Cell0035.execution SourceMainBudgetV1.Cell0035.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=36) (input:=SourceMainFramesV1.Point0036.input) (pair:=SourceMainFramesV1.Point0036.outputs) SourceHeightEdgesV1.Edge0036.left_defined SourceMainFramesV1.Point0036.input_defined SourceMainFramesV1.Point0036.outputs_defined SourceMainBudgetV1.Cell0036.execution SourceMainBudgetV1.Cell0036.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=37) (input:=SourceMainFramesV1.Point0037.input) (pair:=SourceMainFramesV1.Point0037.outputs) SourceHeightEdgesV1.Edge0037.left_defined SourceMainFramesV1.Point0037.input_defined SourceMainFramesV1.Point0037.outputs_defined SourceMainBudgetV1.Cell0037.execution SourceMainBudgetV1.Cell0037.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=38) (input:=SourceMainFramesV1.Point0038.input) (pair:=SourceMainFramesV1.Point0038.outputs) SourceHeightEdgesV1.Edge0038.left_defined SourceMainFramesV1.Point0038.input_defined SourceMainFramesV1.Point0038.outputs_defined SourceMainBudgetV1.Cell0038.execution SourceMainBudgetV1.Cell0038.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=39) (input:=SourceMainFramesV1.Point0039.input) (pair:=SourceMainFramesV1.Point0039.outputs) SourceHeightEdgesV1.Edge0039.left_defined SourceMainFramesV1.Point0039.input_defined SourceMainFramesV1.Point0039.outputs_defined SourceMainBudgetV1.Cell0039.execution SourceMainBudgetV1.Cell0039.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=40) (input:=SourceMainFramesV1.Point0040.input) (pair:=SourceMainFramesV1.Point0040.outputs) SourceHeightEdgesV1.Edge0040.left_defined SourceMainFramesV1.Point0040.input_defined SourceMainFramesV1.Point0040.outputs_defined SourceMainBudgetV1.Cell0040.execution SourceMainBudgetV1.Cell0040.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=41) (input:=SourceMainFramesV1.Point0041.input) (pair:=SourceMainFramesV1.Point0041.outputs) SourceHeightEdgesV1.Edge0041.left_defined SourceMainFramesV1.Point0041.input_defined SourceMainFramesV1.Point0041.outputs_defined SourceMainBudgetV1.Cell0041.execution SourceMainBudgetV1.Cell0041.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=42) (input:=SourceMainFramesV1.Point0042.input) (pair:=SourceMainFramesV1.Point0042.outputs) SourceHeightEdgesV1.Edge0042.left_defined SourceMainFramesV1.Point0042.input_defined SourceMainFramesV1.Point0042.outputs_defined SourceMainBudgetV1.Cell0042.execution SourceMainBudgetV1.Cell0042.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=43) (input:=SourceMainFramesV1.Point0043.input) (pair:=SourceMainFramesV1.Point0043.outputs) SourceHeightEdgesV1.Edge0043.left_defined SourceMainFramesV1.Point0043.input_defined SourceMainFramesV1.Point0043.outputs_defined SourceMainBudgetV1.Cell0043.execution SourceMainBudgetV1.Cell0043.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=44) (input:=SourceMainFramesV1.Point0044.input) (pair:=SourceMainFramesV1.Point0044.outputs) SourceHeightEdgesV1.Edge0044.left_defined SourceMainFramesV1.Point0044.input_defined SourceMainFramesV1.Point0044.outputs_defined SourceMainBudgetV1.Cell0044.execution SourceMainBudgetV1.Cell0044.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=45) (input:=SourceMainFramesV1.Point0045.input) (pair:=SourceMainFramesV1.Point0045.outputs) SourceHeightEdgesV1.Edge0045.left_defined SourceMainFramesV1.Point0045.input_defined SourceMainFramesV1.Point0045.outputs_defined SourceMainBudgetV1.Cell0045.execution SourceMainBudgetV1.Cell0045.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=46) (input:=SourceMainFramesV1.Point0046.input) (pair:=SourceMainFramesV1.Point0046.outputs) SourceHeightEdgesV1.Edge0046.left_defined SourceMainFramesV1.Point0046.input_defined SourceMainFramesV1.Point0046.outputs_defined SourceMainBudgetV1.Cell0046.execution SourceMainBudgetV1.Cell0046.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=47) (input:=SourceMainFramesV1.Point0047.input) (pair:=SourceMainFramesV1.Point0047.outputs) SourceHeightEdgesV1.Edge0047.left_defined SourceMainFramesV1.Point0047.input_defined SourceMainFramesV1.Point0047.outputs_defined SourceMainBudgetV1.Cell0047.execution SourceMainBudgetV1.Cell0047.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=48) (input:=SourceMainFramesV1.Point0048.input) (pair:=SourceMainFramesV1.Point0048.outputs) SourceHeightEdgesV1.Edge0048.left_defined SourceMainFramesV1.Point0048.input_defined SourceMainFramesV1.Point0048.outputs_defined SourceMainBudgetV1.Cell0048.execution SourceMainBudgetV1.Cell0048.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=49) (input:=SourceMainFramesV1.Point0049.input) (pair:=SourceMainFramesV1.Point0049.outputs) SourceHeightEdgesV1.Edge0049.left_defined SourceMainFramesV1.Point0049.input_defined SourceMainFramesV1.Point0049.outputs_defined SourceMainBudgetV1.Cell0049.execution SourceMainBudgetV1.Cell0049.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=50) (input:=SourceMainFramesV1.Point0050.input) (pair:=SourceMainFramesV1.Point0050.outputs) SourceHeightEdgesV1.Edge0050.left_defined SourceMainFramesV1.Point0050.input_defined SourceMainFramesV1.Point0050.outputs_defined SourceMainBudgetV1.Cell0050.execution SourceMainBudgetV1.Cell0050.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=51) (input:=SourceMainFramesV1.Point0051.input) (pair:=SourceMainFramesV1.Point0051.outputs) SourceHeightEdgesV1.Edge0051.left_defined SourceMainFramesV1.Point0051.input_defined SourceMainFramesV1.Point0051.outputs_defined SourceMainBudgetV1.Cell0051.execution SourceMainBudgetV1.Cell0051.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=52) (input:=SourceMainFramesV1.Point0052.input) (pair:=SourceMainFramesV1.Point0052.outputs) SourceHeightEdgesV1.Edge0052.left_defined SourceMainFramesV1.Point0052.input_defined SourceMainFramesV1.Point0052.outputs_defined SourceMainBudgetV1.Cell0052.execution SourceMainBudgetV1.Cell0052.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=53) (input:=SourceMainFramesV1.Point0053.input) (pair:=SourceMainFramesV1.Point0053.outputs) SourceHeightEdgesV1.Edge0053.left_defined SourceMainFramesV1.Point0053.input_defined SourceMainFramesV1.Point0053.outputs_defined SourceMainBudgetV1.Cell0053.execution SourceMainBudgetV1.Cell0053.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=54) (input:=SourceMainFramesV1.Point0054.input) (pair:=SourceMainFramesV1.Point0054.outputs) SourceHeightEdgesV1.Edge0054.left_defined SourceMainFramesV1.Point0054.input_defined SourceMainFramesV1.Point0054.outputs_defined SourceMainBudgetV1.Cell0054.execution SourceMainBudgetV1.Cell0054.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=55) (input:=SourceMainFramesV1.Point0055.input) (pair:=SourceMainFramesV1.Point0055.outputs) SourceHeightEdgesV1.Edge0055.left_defined SourceMainFramesV1.Point0055.input_defined SourceMainFramesV1.Point0055.outputs_defined SourceMainBudgetV1.Cell0055.execution SourceMainBudgetV1.Cell0055.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=56) (input:=SourceMainFramesV1.Point0056.input) (pair:=SourceMainFramesV1.Point0056.outputs) SourceHeightEdgesV1.Edge0056.left_defined SourceMainFramesV1.Point0056.input_defined SourceMainFramesV1.Point0056.outputs_defined SourceMainBudgetV1.Cell0056.execution SourceMainBudgetV1.Cell0056.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=57) (input:=SourceMainFramesV1.Point0057.input) (pair:=SourceMainFramesV1.Point0057.outputs) SourceHeightEdgesV1.Edge0057.left_defined SourceMainFramesV1.Point0057.input_defined SourceMainFramesV1.Point0057.outputs_defined SourceMainBudgetV1.Cell0057.execution SourceMainBudgetV1.Cell0057.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=58) (input:=SourceMainFramesV1.Point0058.input) (pair:=SourceMainFramesV1.Point0058.outputs) SourceHeightEdgesV1.Edge0058.left_defined SourceMainFramesV1.Point0058.input_defined SourceMainFramesV1.Point0058.outputs_defined SourceMainBudgetV1.Cell0058.execution SourceMainBudgetV1.Cell0058.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=59) (input:=SourceMainFramesV1.Point0059.input) (pair:=SourceMainFramesV1.Point0059.outputs) SourceHeightEdgesV1.Edge0059.left_defined SourceMainFramesV1.Point0059.input_defined SourceMainFramesV1.Point0059.outputs_defined SourceMainBudgetV1.Cell0059.execution SourceMainBudgetV1.Cell0059.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=60) (input:=SourceMainFramesV1.Point0060.input) (pair:=SourceMainFramesV1.Point0060.outputs) SourceHeightEdgesV1.Edge0060.left_defined SourceMainFramesV1.Point0060.input_defined SourceMainFramesV1.Point0060.outputs_defined SourceMainBudgetV1.Cell0060.execution SourceMainBudgetV1.Cell0060.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=61) (input:=SourceMainFramesV1.Point0061.input) (pair:=SourceMainFramesV1.Point0061.outputs) SourceHeightEdgesV1.Edge0061.left_defined SourceMainFramesV1.Point0061.input_defined SourceMainFramesV1.Point0061.outputs_defined SourceMainBudgetV1.Cell0061.execution SourceMainBudgetV1.Cell0061.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=62) (input:=SourceMainFramesV1.Point0062.input) (pair:=SourceMainFramesV1.Point0062.outputs) SourceHeightEdgesV1.Edge0062.left_defined SourceMainFramesV1.Point0062.input_defined SourceMainFramesV1.Point0062.outputs_defined SourceMainBudgetV1.Cell0062.execution SourceMainBudgetV1.Cell0062.next_total
 · exact SourceMainBudgetV1.Data.pack (i:=63) (input:=SourceMainFramesV1.Point0063.input) (pair:=SourceMainFramesV1.Point0063.outputs) SourceHeightEdgesV1.Edge0063.left_defined SourceMainFramesV1.Point0063.input_defined SourceMainFramesV1.Point0063.outputs_defined SourceMainBudgetV1.Cell0063.execution SourceMainBudgetV1.Cell0063.next_total
end SourceMainBudgetV1.Block01
open Lean Elab
run_elab do
 let n := `SourceMainBudgetV1.Block01.all
 let env ← getEnv
 let some ci := env.find? n | throwError "missing actual source cell block"
 let ax ← Lean.collectAxioms n
 logInfo m!"BUDGET_BLOCK_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"
