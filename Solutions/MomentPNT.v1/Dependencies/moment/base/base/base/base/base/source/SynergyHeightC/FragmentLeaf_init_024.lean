import SynergyHeightC.FragmentData
import ScopedC.SourceBundle.FunctionTree
namespace SynergyHeightC.FragmentProofs
open ScopedC.Syntax ScopedC.SourceBundle
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false
def file_initStmt24 : File := ⟨"function_initializePointConstants_stmt024.inc",include_str "../../height-bundle-source-v3/function_initializePointConstants_stmt024.inc"⟩
def fragment_initStmt24 : FunctionTree.StatementFragment := ⟨FragmentData.initStmt24⟩
theorem bound_initStmt24 : FunctionTree.LeafBound fragment_initStmt24 file_initStmt24 := by unfold FunctionTree.LeafBound; decide +kernel
def file_initStmt25 : File := ⟨"function_initializePointConstants_stmt025.inc",include_str "../../height-bundle-source-v3/function_initializePointConstants_stmt025.inc"⟩
def fragment_initStmt25 : FunctionTree.StatementFragment := ⟨FragmentData.initStmt25⟩
theorem bound_initStmt25 : FunctionTree.LeafBound fragment_initStmt25 file_initStmt25 := by unfold FunctionTree.LeafBound; decide +kernel
def file_initStmt26 : File := ⟨"function_initializePointConstants_stmt026.inc",include_str "../../height-bundle-source-v3/function_initializePointConstants_stmt026.inc"⟩
def fragment_initStmt26 : FunctionTree.StatementFragment := ⟨FragmentData.initStmt26⟩
theorem bound_initStmt26 : FunctionTree.LeafBound fragment_initStmt26 file_initStmt26 := by unfold FunctionTree.LeafBound; decide +kernel
def file_initStmt27 : File := ⟨"function_initializePointConstants_stmt027.inc",include_str "../../height-bundle-source-v3/function_initializePointConstants_stmt027.inc"⟩
def fragment_initStmt27 : FunctionTree.StatementFragment := ⟨FragmentData.initStmt27⟩
theorem bound_initStmt27 : FunctionTree.LeafBound fragment_initStmt27 file_initStmt27 := by unfold FunctionTree.LeafBound; decide +kernel
def file_initStmt28 : File := ⟨"function_initializePointConstants_stmt028.inc",include_str "../../height-bundle-source-v3/function_initializePointConstants_stmt028.inc"⟩
def fragment_initStmt28 : FunctionTree.StatementFragment := ⟨FragmentData.initStmt28⟩
theorem bound_initStmt28 : FunctionTree.LeafBound fragment_initStmt28 file_initStmt28 := by unfold FunctionTree.LeafBound; decide +kernel
def file_initStmt29 : File := ⟨"function_initializePointConstants_stmt029.inc",include_str "../../height-bundle-source-v3/function_initializePointConstants_stmt029.inc"⟩
def fragment_initStmt29 : FunctionTree.StatementFragment := ⟨FragmentData.initStmt29⟩
theorem bound_initStmt29 : FunctionTree.LeafBound fragment_initStmt29 file_initStmt29 := by unfold FunctionTree.LeafBound; decide +kernel
def file_initStmt30 : File := ⟨"function_initializePointConstants_stmt030.inc",include_str "../../height-bundle-source-v3/function_initializePointConstants_stmt030.inc"⟩
def fragment_initStmt30 : FunctionTree.StatementFragment := ⟨FragmentData.initStmt30⟩
theorem bound_initStmt30 : FunctionTree.LeafBound fragment_initStmt30 file_initStmt30 := by unfold FunctionTree.LeafBound; decide +kernel
def file_initStmt31 : File := ⟨"function_initializePointConstants_stmt031.inc",include_str "../../height-bundle-source-v3/function_initializePointConstants_stmt031.inc"⟩
def fragment_initStmt31 : FunctionTree.StatementFragment := ⟨FragmentData.initStmt31⟩
theorem bound_initStmt31 : FunctionTree.LeafBound fragment_initStmt31 file_initStmt31 := by unfold FunctionTree.LeafBound; decide +kernel
#print axioms bound_initStmt24
#print axioms bound_initStmt25
#print axioms bound_initStmt26
#print axioms bound_initStmt27
#print axioms bound_initStmt28
#print axioms bound_initStmt29
#print axioms bound_initStmt30
#print axioms bound_initStmt31
end SynergyHeightC.FragmentProofs
