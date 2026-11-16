import SynergyHeightC.FragmentData
import ScopedC.SourceBundle.FunctionTree
namespace SynergyHeightC.FragmentProofs
open ScopedC.Syntax ScopedC.SourceBundle
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false
def file_pointStmt64 : File := ⟨"function_pointHeight_stmt064.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt064.inc"⟩
def fragment_pointStmt64 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt64⟩
theorem bound_pointStmt64 : FunctionTree.LeafBound fragment_pointStmt64 file_pointStmt64 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt65 : File := ⟨"function_pointHeight_stmt065.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt065.inc"⟩
def fragment_pointStmt65 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt65⟩
theorem bound_pointStmt65 : FunctionTree.LeafBound fragment_pointStmt65 file_pointStmt65 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt66 : File := ⟨"function_pointHeight_stmt066.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt066.inc"⟩
def fragment_pointStmt66 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt66⟩
theorem bound_pointStmt66 : FunctionTree.LeafBound fragment_pointStmt66 file_pointStmt66 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt67 : File := ⟨"function_pointHeight_stmt067.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt067.inc"⟩
def fragment_pointStmt67 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt67⟩
theorem bound_pointStmt67 : FunctionTree.LeafBound fragment_pointStmt67 file_pointStmt67 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt68 : File := ⟨"function_pointHeight_stmt068.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt068.inc"⟩
def fragment_pointStmt68 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt68⟩
theorem bound_pointStmt68 : FunctionTree.LeafBound fragment_pointStmt68 file_pointStmt68 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt69 : File := ⟨"function_pointHeight_stmt069.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt069.inc"⟩
def fragment_pointStmt69 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt69⟩
theorem bound_pointStmt69 : FunctionTree.LeafBound fragment_pointStmt69 file_pointStmt69 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt70 : File := ⟨"function_pointHeight_stmt070.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt070.inc"⟩
def fragment_pointStmt70 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt70⟩
theorem bound_pointStmt70 : FunctionTree.LeafBound fragment_pointStmt70 file_pointStmt70 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt71 : File := ⟨"function_pointHeight_stmt071.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt071.inc"⟩
def fragment_pointStmt71 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt71⟩
theorem bound_pointStmt71 : FunctionTree.LeafBound fragment_pointStmt71 file_pointStmt71 := by unfold FunctionTree.LeafBound; decide +kernel
#print axioms bound_pointStmt64
#print axioms bound_pointStmt65
#print axioms bound_pointStmt66
#print axioms bound_pointStmt67
#print axioms bound_pointStmt68
#print axioms bound_pointStmt69
#print axioms bound_pointStmt70
#print axioms bound_pointStmt71
end SynergyHeightC.FragmentProofs
