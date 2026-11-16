import SynergyHeightC.FragmentData
import ScopedC.SourceBundle.FunctionTree
namespace SynergyHeightC.FragmentProofs
open ScopedC.Syntax ScopedC.SourceBundle
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false
def file_pointStmt56 : File := ⟨"function_pointHeight_stmt056.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt056.inc"⟩
def fragment_pointStmt56 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt56⟩
theorem bound_pointStmt56 : FunctionTree.LeafBound fragment_pointStmt56 file_pointStmt56 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt57 : File := ⟨"function_pointHeight_stmt057.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt057.inc"⟩
def fragment_pointStmt57 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt57⟩
theorem bound_pointStmt57 : FunctionTree.LeafBound fragment_pointStmt57 file_pointStmt57 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt58 : File := ⟨"function_pointHeight_stmt058.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt058.inc"⟩
def fragment_pointStmt58 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt58⟩
theorem bound_pointStmt58 : FunctionTree.LeafBound fragment_pointStmt58 file_pointStmt58 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt59 : File := ⟨"function_pointHeight_stmt059.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt059.inc"⟩
def fragment_pointStmt59 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt59⟩
theorem bound_pointStmt59 : FunctionTree.LeafBound fragment_pointStmt59 file_pointStmt59 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt60 : File := ⟨"function_pointHeight_stmt060.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt060.inc"⟩
def fragment_pointStmt60 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt60⟩
theorem bound_pointStmt60 : FunctionTree.LeafBound fragment_pointStmt60 file_pointStmt60 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt61 : File := ⟨"function_pointHeight_stmt061.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt061.inc"⟩
def fragment_pointStmt61 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt61⟩
theorem bound_pointStmt61 : FunctionTree.LeafBound fragment_pointStmt61 file_pointStmt61 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt62 : File := ⟨"function_pointHeight_stmt062.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt062.inc"⟩
def fragment_pointStmt62 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt62⟩
theorem bound_pointStmt62 : FunctionTree.LeafBound fragment_pointStmt62 file_pointStmt62 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt63 : File := ⟨"function_pointHeight_stmt063.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt063.inc"⟩
def fragment_pointStmt63 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt63⟩
theorem bound_pointStmt63 : FunctionTree.LeafBound fragment_pointStmt63 file_pointStmt63 := by unfold FunctionTree.LeafBound; decide +kernel
#print axioms bound_pointStmt56
#print axioms bound_pointStmt57
#print axioms bound_pointStmt58
#print axioms bound_pointStmt59
#print axioms bound_pointStmt60
#print axioms bound_pointStmt61
#print axioms bound_pointStmt62
#print axioms bound_pointStmt63
end SynergyHeightC.FragmentProofs
