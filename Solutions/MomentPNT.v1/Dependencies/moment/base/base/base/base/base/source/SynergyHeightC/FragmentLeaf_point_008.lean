import SynergyHeightC.FragmentData
import ScopedC.SourceBundle.FunctionTree
namespace SynergyHeightC.FragmentProofs
open ScopedC.Syntax ScopedC.SourceBundle
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false
def file_pointStmt8 : File := ⟨"function_pointHeight_stmt008.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt008.inc"⟩
def fragment_pointStmt8 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt8⟩
theorem bound_pointStmt8 : FunctionTree.LeafBound fragment_pointStmt8 file_pointStmt8 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt9 : File := ⟨"function_pointHeight_stmt009.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt009.inc"⟩
def fragment_pointStmt9 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt9⟩
theorem bound_pointStmt9 : FunctionTree.LeafBound fragment_pointStmt9 file_pointStmt9 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt10 : File := ⟨"function_pointHeight_stmt010.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt010.inc"⟩
def fragment_pointStmt10 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt10⟩
theorem bound_pointStmt10 : FunctionTree.LeafBound fragment_pointStmt10 file_pointStmt10 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt11 : File := ⟨"function_pointHeight_stmt011.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt011.inc"⟩
def fragment_pointStmt11 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt11⟩
theorem bound_pointStmt11 : FunctionTree.LeafBound fragment_pointStmt11 file_pointStmt11 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt12 : File := ⟨"function_pointHeight_stmt012.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt012.inc"⟩
def fragment_pointStmt12 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt12⟩
theorem bound_pointStmt12 : FunctionTree.LeafBound fragment_pointStmt12 file_pointStmt12 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt13 : File := ⟨"function_pointHeight_stmt013.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt013.inc"⟩
def fragment_pointStmt13 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt13⟩
theorem bound_pointStmt13 : FunctionTree.LeafBound fragment_pointStmt13 file_pointStmt13 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt14 : File := ⟨"function_pointHeight_stmt014.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt014.inc"⟩
def fragment_pointStmt14 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt14⟩
theorem bound_pointStmt14 : FunctionTree.LeafBound fragment_pointStmt14 file_pointStmt14 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt15 : File := ⟨"function_pointHeight_stmt015.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt015.inc"⟩
def fragment_pointStmt15 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt15⟩
theorem bound_pointStmt15 : FunctionTree.LeafBound fragment_pointStmt15 file_pointStmt15 := by unfold FunctionTree.LeafBound; decide +kernel
#print axioms bound_pointStmt8
#print axioms bound_pointStmt9
#print axioms bound_pointStmt10
#print axioms bound_pointStmt11
#print axioms bound_pointStmt12
#print axioms bound_pointStmt13
#print axioms bound_pointStmt14
#print axioms bound_pointStmt15
end SynergyHeightC.FragmentProofs
