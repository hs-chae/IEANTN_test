import SynergyHeightC.FragmentData
import ScopedC.SourceBundle.FunctionTree
namespace SynergyHeightC.FragmentProofs
open ScopedC.Syntax ScopedC.SourceBundle
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false
def file_pointStmt32 : File := ⟨"function_pointHeight_stmt032.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt032.inc"⟩
def fragment_pointStmt32 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt32⟩
theorem bound_pointStmt32 : FunctionTree.LeafBound fragment_pointStmt32 file_pointStmt32 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt33 : File := ⟨"function_pointHeight_stmt033.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt033.inc"⟩
def fragment_pointStmt33 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt33⟩
theorem bound_pointStmt33 : FunctionTree.LeafBound fragment_pointStmt33 file_pointStmt33 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt34 : File := ⟨"function_pointHeight_stmt034.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt034.inc"⟩
def fragment_pointStmt34 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt34⟩
theorem bound_pointStmt34 : FunctionTree.LeafBound fragment_pointStmt34 file_pointStmt34 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt35 : File := ⟨"function_pointHeight_stmt035.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt035.inc"⟩
def fragment_pointStmt35 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt35⟩
theorem bound_pointStmt35 : FunctionTree.LeafBound fragment_pointStmt35 file_pointStmt35 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt36 : File := ⟨"function_pointHeight_stmt036.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt036.inc"⟩
def fragment_pointStmt36 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt36⟩
theorem bound_pointStmt36 : FunctionTree.LeafBound fragment_pointStmt36 file_pointStmt36 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt37 : File := ⟨"function_pointHeight_stmt037.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt037.inc"⟩
def fragment_pointStmt37 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt37⟩
theorem bound_pointStmt37 : FunctionTree.LeafBound fragment_pointStmt37 file_pointStmt37 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt38 : File := ⟨"function_pointHeight_stmt038.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt038.inc"⟩
def fragment_pointStmt38 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt38⟩
theorem bound_pointStmt38 : FunctionTree.LeafBound fragment_pointStmt38 file_pointStmt38 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt39 : File := ⟨"function_pointHeight_stmt039.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt039.inc"⟩
def fragment_pointStmt39 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt39⟩
theorem bound_pointStmt39 : FunctionTree.LeafBound fragment_pointStmt39 file_pointStmt39 := by unfold FunctionTree.LeafBound; decide +kernel
#print axioms bound_pointStmt32
#print axioms bound_pointStmt33
#print axioms bound_pointStmt34
#print axioms bound_pointStmt35
#print axioms bound_pointStmt36
#print axioms bound_pointStmt37
#print axioms bound_pointStmt38
#print axioms bound_pointStmt39
end SynergyHeightC.FragmentProofs
