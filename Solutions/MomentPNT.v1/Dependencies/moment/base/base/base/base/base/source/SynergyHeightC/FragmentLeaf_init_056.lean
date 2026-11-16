import SynergyHeightC.FragmentData
import ScopedC.SourceBundle.FunctionTree
namespace SynergyHeightC.FragmentProofs
open ScopedC.Syntax ScopedC.SourceBundle
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false
def file_initStmt56 : File := ⟨"function_initializePointConstants_stmt056.inc",include_str "../../height-bundle-source-v3/function_initializePointConstants_stmt056.inc"⟩
def fragment_initStmt56 : FunctionTree.StatementFragment := ⟨FragmentData.initStmt56⟩
theorem bound_initStmt56 : FunctionTree.LeafBound fragment_initStmt56 file_initStmt56 := by unfold FunctionTree.LeafBound; decide +kernel
def file_initStmt57 : File := ⟨"function_initializePointConstants_stmt057.inc",include_str "../../height-bundle-source-v3/function_initializePointConstants_stmt057.inc"⟩
def fragment_initStmt57 : FunctionTree.StatementFragment := ⟨FragmentData.initStmt57⟩
theorem bound_initStmt57 : FunctionTree.LeafBound fragment_initStmt57 file_initStmt57 := by unfold FunctionTree.LeafBound; decide +kernel
def file_initStmt58 : File := ⟨"function_initializePointConstants_stmt058.inc",include_str "../../height-bundle-source-v3/function_initializePointConstants_stmt058.inc"⟩
def fragment_initStmt58 : FunctionTree.StatementFragment := ⟨FragmentData.initStmt58⟩
theorem bound_initStmt58 : FunctionTree.LeafBound fragment_initStmt58 file_initStmt58 := by unfold FunctionTree.LeafBound; decide +kernel
def file_initStmt59 : File := ⟨"function_initializePointConstants_stmt059.inc",include_str "../../height-bundle-source-v3/function_initializePointConstants_stmt059.inc"⟩
def fragment_initStmt59 : FunctionTree.StatementFragment := ⟨FragmentData.initStmt59⟩
theorem bound_initStmt59 : FunctionTree.LeafBound fragment_initStmt59 file_initStmt59 := by unfold FunctionTree.LeafBound; decide +kernel
#print axioms bound_initStmt56
#print axioms bound_initStmt57
#print axioms bound_initStmt58
#print axioms bound_initStmt59
end SynergyHeightC.FragmentProofs
