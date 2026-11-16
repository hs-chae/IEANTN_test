import SynergyHeightC.FragmentData
import ScopedC.SourceBundle.FunctionTree
namespace SynergyHeightC.FragmentProofs
open ScopedC.Syntax ScopedC.SourceBundle
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false
def file_pointStmt104 : File := ⟨"function_pointHeight_stmt104.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt104.inc"⟩
def fragment_pointStmt104 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt104⟩
theorem bound_pointStmt104 : FunctionTree.LeafBound fragment_pointStmt104 file_pointStmt104 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt105 : File := ⟨"function_pointHeight_stmt105.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt105.inc"⟩
def fragment_pointStmt105 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt105⟩
theorem bound_pointStmt105 : FunctionTree.LeafBound fragment_pointStmt105 file_pointStmt105 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt106 : File := ⟨"function_pointHeight_stmt106.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt106.inc"⟩
def fragment_pointStmt106 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt106⟩
theorem bound_pointStmt106 : FunctionTree.LeafBound fragment_pointStmt106 file_pointStmt106 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt107 : File := ⟨"function_pointHeight_stmt107.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt107.inc"⟩
def fragment_pointStmt107 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt107⟩
theorem bound_pointStmt107 : FunctionTree.LeafBound fragment_pointStmt107 file_pointStmt107 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt108 : File := ⟨"function_pointHeight_stmt108.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt108.inc"⟩
def fragment_pointStmt108 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt108⟩
theorem bound_pointStmt108 : FunctionTree.LeafBound fragment_pointStmt108 file_pointStmt108 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt109 : File := ⟨"function_pointHeight_stmt109.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt109.inc"⟩
def fragment_pointStmt109 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt109⟩
theorem bound_pointStmt109 : FunctionTree.LeafBound fragment_pointStmt109 file_pointStmt109 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt110 : File := ⟨"function_pointHeight_stmt110.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt110.inc"⟩
def fragment_pointStmt110 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt110⟩
theorem bound_pointStmt110 : FunctionTree.LeafBound fragment_pointStmt110 file_pointStmt110 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt111 : File := ⟨"function_pointHeight_stmt111.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt111.inc"⟩
def fragment_pointStmt111 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt111⟩
theorem bound_pointStmt111 : FunctionTree.LeafBound fragment_pointStmt111 file_pointStmt111 := by unfold FunctionTree.LeafBound; decide +kernel
#print axioms bound_pointStmt104
#print axioms bound_pointStmt105
#print axioms bound_pointStmt106
#print axioms bound_pointStmt107
#print axioms bound_pointStmt108
#print axioms bound_pointStmt109
#print axioms bound_pointStmt110
#print axioms bound_pointStmt111
end SynergyHeightC.FragmentProofs
