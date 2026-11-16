import SynergyHeightC.FragmentData
import ScopedC.SourceBundle.FunctionTree
namespace SynergyHeightC.FragmentProofs
open ScopedC.Syntax ScopedC.SourceBundle
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false
def file_pointStmt24 : File := ⟨"function_pointHeight_stmt024.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt024.inc"⟩
def fragment_pointStmt24 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt24⟩
theorem bound_pointStmt24 : FunctionTree.LeafBound fragment_pointStmt24 file_pointStmt24 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt25 : File := ⟨"function_pointHeight_stmt025.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt025.inc"⟩
def fragment_pointStmt25 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt25⟩
theorem bound_pointStmt25 : FunctionTree.LeafBound fragment_pointStmt25 file_pointStmt25 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt26 : File := ⟨"function_pointHeight_stmt026.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt026.inc"⟩
def fragment_pointStmt26 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt26⟩
theorem bound_pointStmt26 : FunctionTree.LeafBound fragment_pointStmt26 file_pointStmt26 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt27 : File := ⟨"function_pointHeight_stmt027.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt027.inc"⟩
def fragment_pointStmt27 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt27⟩
theorem bound_pointStmt27 : FunctionTree.LeafBound fragment_pointStmt27 file_pointStmt27 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt28 : File := ⟨"function_pointHeight_stmt028.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt028.inc"⟩
def fragment_pointStmt28 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt28⟩
theorem bound_pointStmt28 : FunctionTree.LeafBound fragment_pointStmt28 file_pointStmt28 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt29 : File := ⟨"function_pointHeight_stmt029.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt029.inc"⟩
def fragment_pointStmt29 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt29⟩
theorem bound_pointStmt29 : FunctionTree.LeafBound fragment_pointStmt29 file_pointStmt29 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt30 : File := ⟨"function_pointHeight_stmt030.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt030.inc"⟩
def fragment_pointStmt30 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt30⟩
theorem bound_pointStmt30 : FunctionTree.LeafBound fragment_pointStmt30 file_pointStmt30 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt31 : File := ⟨"function_pointHeight_stmt031.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt031.inc"⟩
def fragment_pointStmt31 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt31⟩
theorem bound_pointStmt31 : FunctionTree.LeafBound fragment_pointStmt31 file_pointStmt31 := by unfold FunctionTree.LeafBound; decide +kernel
#print axioms bound_pointStmt24
#print axioms bound_pointStmt25
#print axioms bound_pointStmt26
#print axioms bound_pointStmt27
#print axioms bound_pointStmt28
#print axioms bound_pointStmt29
#print axioms bound_pointStmt30
#print axioms bound_pointStmt31
end SynergyHeightC.FragmentProofs
