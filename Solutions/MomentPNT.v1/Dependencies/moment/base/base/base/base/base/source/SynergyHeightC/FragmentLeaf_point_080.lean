import SynergyHeightC.FragmentData
import ScopedC.SourceBundle.FunctionTree
namespace SynergyHeightC.FragmentProofs
open ScopedC.Syntax ScopedC.SourceBundle
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false
def file_pointStmt80 : File := ⟨"function_pointHeight_stmt080.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt080.inc"⟩
def fragment_pointStmt80 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt80⟩
theorem bound_pointStmt80 : FunctionTree.LeafBound fragment_pointStmt80 file_pointStmt80 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt81 : File := ⟨"function_pointHeight_stmt081.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt081.inc"⟩
def fragment_pointStmt81 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt81⟩
theorem bound_pointStmt81 : FunctionTree.LeafBound fragment_pointStmt81 file_pointStmt81 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt82 : File := ⟨"function_pointHeight_stmt082.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt082.inc"⟩
def fragment_pointStmt82 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt82⟩
theorem bound_pointStmt82 : FunctionTree.LeafBound fragment_pointStmt82 file_pointStmt82 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt83 : File := ⟨"function_pointHeight_stmt083.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt083.inc"⟩
def fragment_pointStmt83 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt83⟩
theorem bound_pointStmt83 : FunctionTree.LeafBound fragment_pointStmt83 file_pointStmt83 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt84 : File := ⟨"function_pointHeight_stmt084.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt084.inc"⟩
def fragment_pointStmt84 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt84⟩
theorem bound_pointStmt84 : FunctionTree.LeafBound fragment_pointStmt84 file_pointStmt84 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt85 : File := ⟨"function_pointHeight_stmt085.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt085.inc"⟩
def fragment_pointStmt85 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt85⟩
theorem bound_pointStmt85 : FunctionTree.LeafBound fragment_pointStmt85 file_pointStmt85 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt86 : File := ⟨"function_pointHeight_stmt086.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt086.inc"⟩
def fragment_pointStmt86 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt86⟩
theorem bound_pointStmt86 : FunctionTree.LeafBound fragment_pointStmt86 file_pointStmt86 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt87 : File := ⟨"function_pointHeight_stmt087.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt087.inc"⟩
def fragment_pointStmt87 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt87⟩
theorem bound_pointStmt87 : FunctionTree.LeafBound fragment_pointStmt87 file_pointStmt87 := by unfold FunctionTree.LeafBound; decide +kernel
#print axioms bound_pointStmt80
#print axioms bound_pointStmt81
#print axioms bound_pointStmt82
#print axioms bound_pointStmt83
#print axioms bound_pointStmt84
#print axioms bound_pointStmt85
#print axioms bound_pointStmt86
#print axioms bound_pointStmt87
end SynergyHeightC.FragmentProofs
