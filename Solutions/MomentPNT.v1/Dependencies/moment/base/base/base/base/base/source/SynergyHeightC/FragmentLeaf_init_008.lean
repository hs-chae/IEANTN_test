import SynergyHeightC.FragmentData
import ScopedC.SourceBundle.FunctionTree
namespace SynergyHeightC.FragmentProofs
open ScopedC.Syntax ScopedC.SourceBundle
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false
def file_initStmt8 : File := ⟨"function_initializePointConstants_stmt008.inc",include_str "../../height-bundle-source-v3/function_initializePointConstants_stmt008.inc"⟩
def fragment_initStmt8 : FunctionTree.StatementFragment := ⟨FragmentData.initStmt8⟩
theorem bound_initStmt8 : FunctionTree.LeafBound fragment_initStmt8 file_initStmt8 := by unfold FunctionTree.LeafBound; decide +kernel
def file_initStmt9 : File := ⟨"function_initializePointConstants_stmt009.inc",include_str "../../height-bundle-source-v3/function_initializePointConstants_stmt009.inc"⟩
def fragment_initStmt9 : FunctionTree.StatementFragment := ⟨FragmentData.initStmt9⟩
theorem bound_initStmt9 : FunctionTree.LeafBound fragment_initStmt9 file_initStmt9 := by unfold FunctionTree.LeafBound; decide +kernel
def file_initStmt10 : File := ⟨"function_initializePointConstants_stmt010.inc",include_str "../../height-bundle-source-v3/function_initializePointConstants_stmt010.inc"⟩
def fragment_initStmt10 : FunctionTree.StatementFragment := ⟨FragmentData.initStmt10⟩
theorem bound_initStmt10 : FunctionTree.LeafBound fragment_initStmt10 file_initStmt10 := by unfold FunctionTree.LeafBound; decide +kernel
def file_initStmt11 : File := ⟨"function_initializePointConstants_stmt011.inc",include_str "../../height-bundle-source-v3/function_initializePointConstants_stmt011.inc"⟩
def fragment_initStmt11 : FunctionTree.StatementFragment := ⟨FragmentData.initStmt11⟩
theorem bound_initStmt11 : FunctionTree.LeafBound fragment_initStmt11 file_initStmt11 := by unfold FunctionTree.LeafBound; decide +kernel
def file_initStmt12 : File := ⟨"function_initializePointConstants_stmt012.inc",include_str "../../height-bundle-source-v3/function_initializePointConstants_stmt012.inc"⟩
def fragment_initStmt12 : FunctionTree.StatementFragment := ⟨FragmentData.initStmt12⟩
theorem bound_initStmt12 : FunctionTree.LeafBound fragment_initStmt12 file_initStmt12 := by unfold FunctionTree.LeafBound; decide +kernel
def file_initStmt13 : File := ⟨"function_initializePointConstants_stmt013.inc",include_str "../../height-bundle-source-v3/function_initializePointConstants_stmt013.inc"⟩
def fragment_initStmt13 : FunctionTree.StatementFragment := ⟨FragmentData.initStmt13⟩
theorem bound_initStmt13 : FunctionTree.LeafBound fragment_initStmt13 file_initStmt13 := by unfold FunctionTree.LeafBound; decide +kernel
def file_initStmt14 : File := ⟨"function_initializePointConstants_stmt014.inc",include_str "../../height-bundle-source-v3/function_initializePointConstants_stmt014.inc"⟩
def fragment_initStmt14 : FunctionTree.StatementFragment := ⟨FragmentData.initStmt14⟩
theorem bound_initStmt14 : FunctionTree.LeafBound fragment_initStmt14 file_initStmt14 := by unfold FunctionTree.LeafBound; decide +kernel
def file_initStmt15 : File := ⟨"function_initializePointConstants_stmt015.inc",include_str "../../height-bundle-source-v3/function_initializePointConstants_stmt015.inc"⟩
def fragment_initStmt15 : FunctionTree.StatementFragment := ⟨FragmentData.initStmt15⟩
theorem bound_initStmt15 : FunctionTree.LeafBound fragment_initStmt15 file_initStmt15 := by unfold FunctionTree.LeafBound; decide +kernel
#print axioms bound_initStmt8
#print axioms bound_initStmt9
#print axioms bound_initStmt10
#print axioms bound_initStmt11
#print axioms bound_initStmt12
#print axioms bound_initStmt13
#print axioms bound_initStmt14
#print axioms bound_initStmt15
end SynergyHeightC.FragmentProofs
