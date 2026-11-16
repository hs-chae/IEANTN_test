import SynergyHeightC.FragmentData
import ScopedC.SourceBundle.FunctionTree
namespace SynergyHeightC.FragmentProofs
open ScopedC.Syntax ScopedC.SourceBundle
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false
def file_edgeStmt0 : File := ⟨"function_pointEdge_stmt000.inc",include_str "../../height-bundle-source-v3/function_pointEdge_stmt000.inc"⟩
def fragment_edgeStmt0 : FunctionTree.StatementFragment := ⟨FragmentData.edgeStmt0⟩
theorem bound_edgeStmt0 : FunctionTree.LeafBound fragment_edgeStmt0 file_edgeStmt0 := by unfold FunctionTree.LeafBound; decide +kernel
def file_edgeStmt1 : File := ⟨"function_pointEdge_stmt001.inc",include_str "../../height-bundle-source-v3/function_pointEdge_stmt001.inc"⟩
def fragment_edgeStmt1 : FunctionTree.StatementFragment := ⟨FragmentData.edgeStmt1⟩
theorem bound_edgeStmt1 : FunctionTree.LeafBound fragment_edgeStmt1 file_edgeStmt1 := by unfold FunctionTree.LeafBound; decide +kernel
def file_edgeStmt2 : File := ⟨"function_pointEdge_stmt002.inc",include_str "../../height-bundle-source-v3/function_pointEdge_stmt002.inc"⟩
def fragment_edgeStmt2 : FunctionTree.StatementFragment := ⟨FragmentData.edgeStmt2⟩
theorem bound_edgeStmt2 : FunctionTree.LeafBound fragment_edgeStmt2 file_edgeStmt2 := by unfold FunctionTree.LeafBound; decide +kernel
def file_edgeStmt3 : File := ⟨"function_pointEdge_stmt003.inc",include_str "../../height-bundle-source-v3/function_pointEdge_stmt003.inc"⟩
def fragment_edgeStmt3 : FunctionTree.StatementFragment := ⟨FragmentData.edgeStmt3⟩
theorem bound_edgeStmt3 : FunctionTree.LeafBound fragment_edgeStmt3 file_edgeStmt3 := by unfold FunctionTree.LeafBound; decide +kernel
#print axioms bound_edgeStmt0
#print axioms bound_edgeStmt1
#print axioms bound_edgeStmt2
#print axioms bound_edgeStmt3
end SynergyHeightC.FragmentProofs
