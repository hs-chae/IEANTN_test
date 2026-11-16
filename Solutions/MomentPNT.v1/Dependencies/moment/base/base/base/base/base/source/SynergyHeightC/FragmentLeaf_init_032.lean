import SynergyHeightC.FragmentData
import ScopedC.SourceBundle.FunctionTree
namespace SynergyHeightC.FragmentProofs
open ScopedC.Syntax ScopedC.SourceBundle
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false
def file_initStmt32 : File := ⟨"function_initializePointConstants_stmt032.inc",include_str "../../height-bundle-source-v3/function_initializePointConstants_stmt032.inc"⟩
def fragment_initStmt32 : FunctionTree.StatementFragment := ⟨FragmentData.initStmt32⟩
theorem bound_initStmt32 : FunctionTree.LeafBound fragment_initStmt32 file_initStmt32 := by unfold FunctionTree.LeafBound; decide +kernel
def file_initStmt33 : File := ⟨"function_initializePointConstants_stmt033.inc",include_str "../../height-bundle-source-v3/function_initializePointConstants_stmt033.inc"⟩
def fragment_initStmt33 : FunctionTree.StatementFragment := ⟨FragmentData.initStmt33⟩
theorem bound_initStmt33 : FunctionTree.LeafBound fragment_initStmt33 file_initStmt33 := by unfold FunctionTree.LeafBound; decide +kernel
def file_initStmt34 : File := ⟨"function_initializePointConstants_stmt034.inc",include_str "../../height-bundle-source-v3/function_initializePointConstants_stmt034.inc"⟩
def fragment_initStmt34 : FunctionTree.StatementFragment := ⟨FragmentData.initStmt34⟩
theorem bound_initStmt34 : FunctionTree.LeafBound fragment_initStmt34 file_initStmt34 := by unfold FunctionTree.LeafBound; decide +kernel
def file_initStmt35 : File := ⟨"function_initializePointConstants_stmt035.inc",include_str "../../height-bundle-source-v3/function_initializePointConstants_stmt035.inc"⟩
def fragment_initStmt35 : FunctionTree.StatementFragment := ⟨FragmentData.initStmt35⟩
theorem bound_initStmt35 : FunctionTree.LeafBound fragment_initStmt35 file_initStmt35 := by unfold FunctionTree.LeafBound; decide +kernel
def file_initStmt36 : File := ⟨"function_initializePointConstants_stmt036.inc",include_str "../../height-bundle-source-v3/function_initializePointConstants_stmt036.inc"⟩
def fragment_initStmt36 : FunctionTree.StatementFragment := ⟨FragmentData.initStmt36⟩
theorem bound_initStmt36 : FunctionTree.LeafBound fragment_initStmt36 file_initStmt36 := by unfold FunctionTree.LeafBound; decide +kernel
def file_initStmt37 : File := ⟨"function_initializePointConstants_stmt037.inc",include_str "../../height-bundle-source-v3/function_initializePointConstants_stmt037.inc"⟩
def fragment_initStmt37 : FunctionTree.StatementFragment := ⟨FragmentData.initStmt37⟩
theorem bound_initStmt37 : FunctionTree.LeafBound fragment_initStmt37 file_initStmt37 := by unfold FunctionTree.LeafBound; decide +kernel
def file_initStmt38 : File := ⟨"function_initializePointConstants_stmt038.inc",include_str "../../height-bundle-source-v3/function_initializePointConstants_stmt038.inc"⟩
def fragment_initStmt38 : FunctionTree.StatementFragment := ⟨FragmentData.initStmt38⟩
theorem bound_initStmt38 : FunctionTree.LeafBound fragment_initStmt38 file_initStmt38 := by unfold FunctionTree.LeafBound; decide +kernel
def file_initStmt39 : File := ⟨"function_initializePointConstants_stmt039.inc",include_str "../../height-bundle-source-v3/function_initializePointConstants_stmt039.inc"⟩
def fragment_initStmt39 : FunctionTree.StatementFragment := ⟨FragmentData.initStmt39⟩
theorem bound_initStmt39 : FunctionTree.LeafBound fragment_initStmt39 file_initStmt39 := by unfold FunctionTree.LeafBound; decide +kernel
#print axioms bound_initStmt32
#print axioms bound_initStmt33
#print axioms bound_initStmt34
#print axioms bound_initStmt35
#print axioms bound_initStmt36
#print axioms bound_initStmt37
#print axioms bound_initStmt38
#print axioms bound_initStmt39
end SynergyHeightC.FragmentProofs
