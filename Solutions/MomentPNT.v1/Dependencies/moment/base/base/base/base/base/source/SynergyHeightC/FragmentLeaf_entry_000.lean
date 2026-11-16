import SynergyHeightC.FragmentData
import ScopedC.SourceBundle.FunctionTree
namespace SynergyHeightC.FragmentProofs
open ScopedC.Syntax ScopedC.SourceBundle
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false
def file_entryStmt0 : File := ⟨"function_main_stmt000.inc",include_str "../../height-bundle-source-v3/function_main_stmt000.inc"⟩
def fragment_entryStmt0 : FunctionTree.StatementFragment := ⟨FragmentData.entryStmt0⟩
theorem bound_entryStmt0 : FunctionTree.LeafBound fragment_entryStmt0 file_entryStmt0 := by unfold FunctionTree.LeafBound; decide +kernel
def file_entryStmt1 : File := ⟨"function_main_stmt001.inc",include_str "../../height-bundle-source-v3/function_main_stmt001.inc"⟩
def fragment_entryStmt1 : FunctionTree.StatementFragment := ⟨FragmentData.entryStmt1⟩
theorem bound_entryStmt1 : FunctionTree.LeafBound fragment_entryStmt1 file_entryStmt1 := by unfold FunctionTree.LeafBound; decide +kernel
def file_entryStmt2 : File := ⟨"function_main_stmt002.inc",include_str "../../height-bundle-source-v3/function_main_stmt002.inc"⟩
def fragment_entryStmt2 : FunctionTree.StatementFragment := ⟨FragmentData.entryStmt2⟩
theorem bound_entryStmt2 : FunctionTree.LeafBound fragment_entryStmt2 file_entryStmt2 := by unfold FunctionTree.LeafBound; decide +kernel
def file_entryStmt3 : File := ⟨"function_main_stmt003.inc",include_str "../../height-bundle-source-v3/function_main_stmt003.inc"⟩
def fragment_entryStmt3 : FunctionTree.StatementFragment := ⟨FragmentData.entryStmt3⟩
theorem bound_entryStmt3 : FunctionTree.LeafBound fragment_entryStmt3 file_entryStmt3 := by unfold FunctionTree.LeafBound; decide +kernel
def file_entryStmt4 : File := ⟨"function_main_stmt004.inc",include_str "../../height-bundle-source-v3/function_main_stmt004.inc"⟩
def fragment_entryStmt4 : FunctionTree.StatementFragment := ⟨FragmentData.entryStmt4⟩
theorem bound_entryStmt4 : FunctionTree.LeafBound fragment_entryStmt4 file_entryStmt4 := by unfold FunctionTree.LeafBound; decide +kernel
def file_entryStmt5 : File := ⟨"function_main_stmt005.inc",include_str "../../height-bundle-source-v3/function_main_stmt005.inc"⟩
def fragment_entryStmt5 : FunctionTree.StatementFragment := ⟨FragmentData.entryStmt5⟩
theorem bound_entryStmt5 : FunctionTree.LeafBound fragment_entryStmt5 file_entryStmt5 := by unfold FunctionTree.LeafBound; decide +kernel
def file_entryStmt6 : File := ⟨"function_main_stmt006.inc",include_str "../../height-bundle-source-v3/function_main_stmt006.inc"⟩
def fragment_entryStmt6 : FunctionTree.StatementFragment := ⟨FragmentData.entryStmt6⟩
theorem bound_entryStmt6 : FunctionTree.LeafBound fragment_entryStmt6 file_entryStmt6 := by unfold FunctionTree.LeafBound; decide +kernel
def file_entryStmt7 : File := ⟨"function_main_stmt007.inc",include_str "../../height-bundle-source-v3/function_main_stmt007.inc"⟩
def fragment_entryStmt7 : FunctionTree.StatementFragment := ⟨FragmentData.entryStmt7⟩
theorem bound_entryStmt7 : FunctionTree.LeafBound fragment_entryStmt7 file_entryStmt7 := by unfold FunctionTree.LeafBound; decide +kernel
#print axioms bound_entryStmt0
#print axioms bound_entryStmt1
#print axioms bound_entryStmt2
#print axioms bound_entryStmt3
#print axioms bound_entryStmt4
#print axioms bound_entryStmt5
#print axioms bound_entryStmt6
#print axioms bound_entryStmt7
end SynergyHeightC.FragmentProofs
