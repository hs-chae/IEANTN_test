import SynergyHeightC.FragmentData
import ScopedC.SourceBundle.FunctionTree
namespace SynergyHeightC.FragmentProofs
open ScopedC.Syntax ScopedC.SourceBundle
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false
def file_initStmt48 : File := ⟨"function_initializePointConstants_stmt048.inc",include_str "../../height-bundle-source-v3/function_initializePointConstants_stmt048.inc"⟩
def fragment_initStmt48 : FunctionTree.StatementFragment := ⟨FragmentData.initStmt48⟩
theorem bound_initStmt48 : FunctionTree.LeafBound fragment_initStmt48 file_initStmt48 := by unfold FunctionTree.LeafBound; decide +kernel
def file_initStmt49 : File := ⟨"function_initializePointConstants_stmt049.inc",include_str "../../height-bundle-source-v3/function_initializePointConstants_stmt049.inc"⟩
def fragment_initStmt49 : FunctionTree.StatementFragment := ⟨FragmentData.initStmt49⟩
theorem bound_initStmt49 : FunctionTree.LeafBound fragment_initStmt49 file_initStmt49 := by unfold FunctionTree.LeafBound; decide +kernel
def file_initStmt50 : File := ⟨"function_initializePointConstants_stmt050.inc",include_str "../../height-bundle-source-v3/function_initializePointConstants_stmt050.inc"⟩
def fragment_initStmt50 : FunctionTree.StatementFragment := ⟨FragmentData.initStmt50⟩
theorem bound_initStmt50 : FunctionTree.LeafBound fragment_initStmt50 file_initStmt50 := by unfold FunctionTree.LeafBound; decide +kernel
def file_initStmt51 : File := ⟨"function_initializePointConstants_stmt051.inc",include_str "../../height-bundle-source-v3/function_initializePointConstants_stmt051.inc"⟩
def fragment_initStmt51 : FunctionTree.StatementFragment := ⟨FragmentData.initStmt51⟩
theorem bound_initStmt51 : FunctionTree.LeafBound fragment_initStmt51 file_initStmt51 := by unfold FunctionTree.LeafBound; decide +kernel
def file_initStmt52 : File := ⟨"function_initializePointConstants_stmt052.inc",include_str "../../height-bundle-source-v3/function_initializePointConstants_stmt052.inc"⟩
def fragment_initStmt52 : FunctionTree.StatementFragment := ⟨FragmentData.initStmt52⟩
theorem bound_initStmt52 : FunctionTree.LeafBound fragment_initStmt52 file_initStmt52 := by unfold FunctionTree.LeafBound; decide +kernel
def file_initStmt53 : File := ⟨"function_initializePointConstants_stmt053.inc",include_str "../../height-bundle-source-v3/function_initializePointConstants_stmt053.inc"⟩
def fragment_initStmt53 : FunctionTree.StatementFragment := ⟨FragmentData.initStmt53⟩
theorem bound_initStmt53 : FunctionTree.LeafBound fragment_initStmt53 file_initStmt53 := by unfold FunctionTree.LeafBound; decide +kernel
def file_initStmt54 : File := ⟨"function_initializePointConstants_stmt054.inc",include_str "../../height-bundle-source-v3/function_initializePointConstants_stmt054.inc"⟩
def fragment_initStmt54 : FunctionTree.StatementFragment := ⟨FragmentData.initStmt54⟩
theorem bound_initStmt54 : FunctionTree.LeafBound fragment_initStmt54 file_initStmt54 := by unfold FunctionTree.LeafBound; decide +kernel
def file_initStmt55 : File := ⟨"function_initializePointConstants_stmt055.inc",include_str "../../height-bundle-source-v3/function_initializePointConstants_stmt055.inc"⟩
def fragment_initStmt55 : FunctionTree.StatementFragment := ⟨FragmentData.initStmt55⟩
theorem bound_initStmt55 : FunctionTree.LeafBound fragment_initStmt55 file_initStmt55 := by unfold FunctionTree.LeafBound; decide +kernel
#print axioms bound_initStmt48
#print axioms bound_initStmt49
#print axioms bound_initStmt50
#print axioms bound_initStmt51
#print axioms bound_initStmt52
#print axioms bound_initStmt53
#print axioms bound_initStmt54
#print axioms bound_initStmt55
end SynergyHeightC.FragmentProofs
