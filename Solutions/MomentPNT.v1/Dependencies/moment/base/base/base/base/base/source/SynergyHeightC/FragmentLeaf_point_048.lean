import SynergyHeightC.FragmentData
import ScopedC.SourceBundle.FunctionTree
namespace SynergyHeightC.FragmentProofs
open ScopedC.Syntax ScopedC.SourceBundle
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false
def file_pointStmt48 : File := ⟨"function_pointHeight_stmt048.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt048.inc"⟩
def fragment_pointStmt48 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt48⟩
theorem bound_pointStmt48 : FunctionTree.LeafBound fragment_pointStmt48 file_pointStmt48 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt49 : File := ⟨"function_pointHeight_stmt049.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt049.inc"⟩
def fragment_pointStmt49 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt49⟩
theorem bound_pointStmt49 : FunctionTree.LeafBound fragment_pointStmt49 file_pointStmt49 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt50 : File := ⟨"function_pointHeight_stmt050.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt050.inc"⟩
def fragment_pointStmt50 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt50⟩
theorem bound_pointStmt50 : FunctionTree.LeafBound fragment_pointStmt50 file_pointStmt50 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt51 : File := ⟨"function_pointHeight_stmt051.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt051.inc"⟩
def fragment_pointStmt51 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt51⟩
theorem bound_pointStmt51 : FunctionTree.LeafBound fragment_pointStmt51 file_pointStmt51 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt52 : File := ⟨"function_pointHeight_stmt052.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt052.inc"⟩
def fragment_pointStmt52 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt52⟩
theorem bound_pointStmt52 : FunctionTree.LeafBound fragment_pointStmt52 file_pointStmt52 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt53 : File := ⟨"function_pointHeight_stmt053.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt053.inc"⟩
def fragment_pointStmt53 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt53⟩
theorem bound_pointStmt53 : FunctionTree.LeafBound fragment_pointStmt53 file_pointStmt53 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt54 : File := ⟨"function_pointHeight_stmt054.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt054.inc"⟩
def fragment_pointStmt54 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt54⟩
theorem bound_pointStmt54 : FunctionTree.LeafBound fragment_pointStmt54 file_pointStmt54 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt55 : File := ⟨"function_pointHeight_stmt055.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt055.inc"⟩
def fragment_pointStmt55 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt55⟩
theorem bound_pointStmt55 : FunctionTree.LeafBound fragment_pointStmt55 file_pointStmt55 := by unfold FunctionTree.LeafBound; decide +kernel
#print axioms bound_pointStmt48
#print axioms bound_pointStmt49
#print axioms bound_pointStmt50
#print axioms bound_pointStmt51
#print axioms bound_pointStmt52
#print axioms bound_pointStmt53
#print axioms bound_pointStmt54
#print axioms bound_pointStmt55
end SynergyHeightC.FragmentProofs
