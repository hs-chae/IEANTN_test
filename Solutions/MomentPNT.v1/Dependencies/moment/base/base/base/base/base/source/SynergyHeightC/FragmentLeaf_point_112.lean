import SynergyHeightC.FragmentData
import ScopedC.SourceBundle.FunctionTree
namespace SynergyHeightC.FragmentProofs
open ScopedC.Syntax ScopedC.SourceBundle
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false
def file_pointStmt112 : File := ⟨"function_pointHeight_stmt112.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt112.inc"⟩
def fragment_pointStmt112 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt112⟩
theorem bound_pointStmt112 : FunctionTree.LeafBound fragment_pointStmt112 file_pointStmt112 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt113 : File := ⟨"function_pointHeight_stmt113.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt113.inc"⟩
def fragment_pointStmt113 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt113⟩
theorem bound_pointStmt113 : FunctionTree.LeafBound fragment_pointStmt113 file_pointStmt113 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt114 : File := ⟨"function_pointHeight_stmt114.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt114.inc"⟩
def fragment_pointStmt114 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt114⟩
theorem bound_pointStmt114 : FunctionTree.LeafBound fragment_pointStmt114 file_pointStmt114 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt115 : File := ⟨"function_pointHeight_stmt115.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt115.inc"⟩
def fragment_pointStmt115 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt115⟩
theorem bound_pointStmt115 : FunctionTree.LeafBound fragment_pointStmt115 file_pointStmt115 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt116 : File := ⟨"function_pointHeight_stmt116.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt116.inc"⟩
def fragment_pointStmt116 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt116⟩
theorem bound_pointStmt116 : FunctionTree.LeafBound fragment_pointStmt116 file_pointStmt116 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt117 : File := ⟨"function_pointHeight_stmt117.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt117.inc"⟩
def fragment_pointStmt117 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt117⟩
theorem bound_pointStmt117 : FunctionTree.LeafBound fragment_pointStmt117 file_pointStmt117 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt118 : File := ⟨"function_pointHeight_stmt118.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt118.inc"⟩
def fragment_pointStmt118 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt118⟩
theorem bound_pointStmt118 : FunctionTree.LeafBound fragment_pointStmt118 file_pointStmt118 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt119 : File := ⟨"function_pointHeight_stmt119.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt119.inc"⟩
def fragment_pointStmt119 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt119⟩
theorem bound_pointStmt119 : FunctionTree.LeafBound fragment_pointStmt119 file_pointStmt119 := by unfold FunctionTree.LeafBound; decide +kernel
#print axioms bound_pointStmt112
#print axioms bound_pointStmt113
#print axioms bound_pointStmt114
#print axioms bound_pointStmt115
#print axioms bound_pointStmt116
#print axioms bound_pointStmt117
#print axioms bound_pointStmt118
#print axioms bound_pointStmt119
end SynergyHeightC.FragmentProofs
