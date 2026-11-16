import SynergyHeightC.FragmentData
import ScopedC.SourceBundle.FunctionTree
namespace SynergyHeightC.FragmentProofs
open ScopedC.Syntax ScopedC.SourceBundle
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false
def file_initStmt0 : File := ⟨"function_initializePointConstants_stmt000.inc",include_str "../../height-bundle-source-v3/function_initializePointConstants_stmt000.inc"⟩
def fragment_initStmt0 : FunctionTree.StatementFragment := ⟨FragmentData.initStmt0⟩
theorem bound_initStmt0 : FunctionTree.LeafBound fragment_initStmt0 file_initStmt0 := by unfold FunctionTree.LeafBound; decide +kernel
def file_initStmt1 : File := ⟨"function_initializePointConstants_stmt001.inc",include_str "../../height-bundle-source-v3/function_initializePointConstants_stmt001.inc"⟩
def fragment_initStmt1 : FunctionTree.StatementFragment := ⟨FragmentData.initStmt1⟩
theorem bound_initStmt1 : FunctionTree.LeafBound fragment_initStmt1 file_initStmt1 := by unfold FunctionTree.LeafBound; decide +kernel
def file_initStmt2 : File := ⟨"function_initializePointConstants_stmt002.inc",include_str "../../height-bundle-source-v3/function_initializePointConstants_stmt002.inc"⟩
def fragment_initStmt2 : FunctionTree.StatementFragment := ⟨FragmentData.initStmt2⟩
theorem bound_initStmt2 : FunctionTree.LeafBound fragment_initStmt2 file_initStmt2 := by unfold FunctionTree.LeafBound; decide +kernel
def file_initStmt3 : File := ⟨"function_initializePointConstants_stmt003.inc",include_str "../../height-bundle-source-v3/function_initializePointConstants_stmt003.inc"⟩
def fragment_initStmt3 : FunctionTree.StatementFragment := ⟨FragmentData.initStmt3⟩
theorem bound_initStmt3 : FunctionTree.LeafBound fragment_initStmt3 file_initStmt3 := by unfold FunctionTree.LeafBound; decide +kernel
def file_initStmt4 : File := ⟨"function_initializePointConstants_stmt004.inc",include_str "../../height-bundle-source-v3/function_initializePointConstants_stmt004.inc"⟩
def fragment_initStmt4 : FunctionTree.StatementFragment := ⟨FragmentData.initStmt4⟩
theorem bound_initStmt4 : FunctionTree.LeafBound fragment_initStmt4 file_initStmt4 := by unfold FunctionTree.LeafBound; decide +kernel
def file_initStmt5 : File := ⟨"function_initializePointConstants_stmt005.inc",include_str "../../height-bundle-source-v3/function_initializePointConstants_stmt005.inc"⟩
def fragment_initStmt5 : FunctionTree.StatementFragment := ⟨FragmentData.initStmt5⟩
theorem bound_initStmt5 : FunctionTree.LeafBound fragment_initStmt5 file_initStmt5 := by unfold FunctionTree.LeafBound; decide +kernel
def file_initStmt6 : File := ⟨"function_initializePointConstants_stmt006.inc",include_str "../../height-bundle-source-v3/function_initializePointConstants_stmt006.inc"⟩
def fragment_initStmt6 : FunctionTree.StatementFragment := ⟨FragmentData.initStmt6⟩
theorem bound_initStmt6 : FunctionTree.LeafBound fragment_initStmt6 file_initStmt6 := by unfold FunctionTree.LeafBound; decide +kernel
def file_initStmt7 : File := ⟨"function_initializePointConstants_stmt007.inc",include_str "../../height-bundle-source-v3/function_initializePointConstants_stmt007.inc"⟩
def fragment_initStmt7 : FunctionTree.StatementFragment := ⟨FragmentData.initStmt7⟩
theorem bound_initStmt7 : FunctionTree.LeafBound fragment_initStmt7 file_initStmt7 := by unfold FunctionTree.LeafBound; decide +kernel
#print axioms bound_initStmt0
#print axioms bound_initStmt1
#print axioms bound_initStmt2
#print axioms bound_initStmt3
#print axioms bound_initStmt4
#print axioms bound_initStmt5
#print axioms bound_initStmt6
#print axioms bound_initStmt7
end SynergyHeightC.FragmentProofs
