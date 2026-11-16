import SynergyHeightC.FragmentData
import ScopedC.SourceBundle.FunctionTree
namespace SynergyHeightC.FragmentProofs
open ScopedC.Syntax ScopedC.SourceBundle
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false
def file_pointStmt96 : File := ⟨"function_pointHeight_stmt096.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt096.inc"⟩
def fragment_pointStmt96 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt96⟩
theorem bound_pointStmt96 : FunctionTree.LeafBound fragment_pointStmt96 file_pointStmt96 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt97 : File := ⟨"function_pointHeight_stmt097.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt097.inc"⟩
def fragment_pointStmt97 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt97⟩
theorem bound_pointStmt97 : FunctionTree.LeafBound fragment_pointStmt97 file_pointStmt97 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt98 : File := ⟨"function_pointHeight_stmt098.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt098.inc"⟩
def fragment_pointStmt98 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt98⟩
theorem bound_pointStmt98 : FunctionTree.LeafBound fragment_pointStmt98 file_pointStmt98 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt99 : File := ⟨"function_pointHeight_stmt099.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt099.inc"⟩
def fragment_pointStmt99 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt99⟩
theorem bound_pointStmt99 : FunctionTree.LeafBound fragment_pointStmt99 file_pointStmt99 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt100 : File := ⟨"function_pointHeight_stmt100.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt100.inc"⟩
def fragment_pointStmt100 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt100⟩
theorem bound_pointStmt100 : FunctionTree.LeafBound fragment_pointStmt100 file_pointStmt100 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt101 : File := ⟨"function_pointHeight_stmt101.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt101.inc"⟩
def fragment_pointStmt101 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt101⟩
theorem bound_pointStmt101 : FunctionTree.LeafBound fragment_pointStmt101 file_pointStmt101 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt102 : File := ⟨"function_pointHeight_stmt102.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt102.inc"⟩
def fragment_pointStmt102 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt102⟩
theorem bound_pointStmt102 : FunctionTree.LeafBound fragment_pointStmt102 file_pointStmt102 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt103 : File := ⟨"function_pointHeight_stmt103.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt103.inc"⟩
def fragment_pointStmt103 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt103⟩
theorem bound_pointStmt103 : FunctionTree.LeafBound fragment_pointStmt103 file_pointStmt103 := by unfold FunctionTree.LeafBound; decide +kernel
#print axioms bound_pointStmt96
#print axioms bound_pointStmt97
#print axioms bound_pointStmt98
#print axioms bound_pointStmt99
#print axioms bound_pointStmt100
#print axioms bound_pointStmt101
#print axioms bound_pointStmt102
#print axioms bound_pointStmt103
end SynergyHeightC.FragmentProofs
