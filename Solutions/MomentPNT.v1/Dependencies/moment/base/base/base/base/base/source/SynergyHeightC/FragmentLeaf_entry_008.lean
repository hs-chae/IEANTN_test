import SynergyHeightC.FragmentData
import ScopedC.SourceBundle.FunctionTree
namespace SynergyHeightC.FragmentProofs
open ScopedC.Syntax ScopedC.SourceBundle
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false
def file_entryStmt8 : File := ⟨"function_main_stmt008.inc",include_str "../../height-bundle-source-v3/function_main_stmt008.inc"⟩
def fragment_entryStmt8 : FunctionTree.StatementFragment := ⟨FragmentData.entryStmt8⟩
theorem bound_entryStmt8 : FunctionTree.LeafBound fragment_entryStmt8 file_entryStmt8 := by unfold FunctionTree.LeafBound; decide +kernel
def file_entryStmt9 : File := ⟨"function_main_stmt009.inc",include_str "../../height-bundle-source-v3/function_main_stmt009.inc"⟩
def fragment_entryStmt9 : FunctionTree.StatementFragment := ⟨FragmentData.entryStmt9⟩
theorem bound_entryStmt9 : FunctionTree.LeafBound fragment_entryStmt9 file_entryStmt9 := by unfold FunctionTree.LeafBound; decide +kernel
#print axioms bound_entryStmt8
#print axioms bound_entryStmt9
end SynergyHeightC.FragmentProofs
