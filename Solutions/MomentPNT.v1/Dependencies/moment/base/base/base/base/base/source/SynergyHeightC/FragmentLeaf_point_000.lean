import SynergyHeightC.FragmentData
import ScopedC.SourceBundle.FunctionTree
namespace SynergyHeightC.FragmentProofs
open ScopedC.Syntax ScopedC.SourceBundle
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false
def file_pointStmt0 : File := ⟨"function_pointHeight_stmt000.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt000.inc"⟩
def fragment_pointStmt0 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt0⟩
theorem bound_pointStmt0 : FunctionTree.LeafBound fragment_pointStmt0 file_pointStmt0 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt1 : File := ⟨"function_pointHeight_stmt001.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt001.inc"⟩
def fragment_pointStmt1 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt1⟩
theorem bound_pointStmt1 : FunctionTree.LeafBound fragment_pointStmt1 file_pointStmt1 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt2 : File := ⟨"function_pointHeight_stmt002.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt002.inc"⟩
def fragment_pointStmt2 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt2⟩
theorem bound_pointStmt2 : FunctionTree.LeafBound fragment_pointStmt2 file_pointStmt2 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt3 : File := ⟨"function_pointHeight_stmt003.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt003.inc"⟩
def fragment_pointStmt3 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt3⟩
theorem bound_pointStmt3 : FunctionTree.LeafBound fragment_pointStmt3 file_pointStmt3 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt4 : File := ⟨"function_pointHeight_stmt004.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt004.inc"⟩
def fragment_pointStmt4 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt4⟩
theorem bound_pointStmt4 : FunctionTree.LeafBound fragment_pointStmt4 file_pointStmt4 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt5 : File := ⟨"function_pointHeight_stmt005.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt005.inc"⟩
def fragment_pointStmt5 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt5⟩
theorem bound_pointStmt5 : FunctionTree.LeafBound fragment_pointStmt5 file_pointStmt5 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt6 : File := ⟨"function_pointHeight_stmt006.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt006.inc"⟩
def fragment_pointStmt6 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt6⟩
theorem bound_pointStmt6 : FunctionTree.LeafBound fragment_pointStmt6 file_pointStmt6 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt7 : File := ⟨"function_pointHeight_stmt007.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt007.inc"⟩
def fragment_pointStmt7 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt7⟩
theorem bound_pointStmt7 : FunctionTree.LeafBound fragment_pointStmt7 file_pointStmt7 := by unfold FunctionTree.LeafBound; decide +kernel
#print axioms bound_pointStmt0
#print axioms bound_pointStmt1
#print axioms bound_pointStmt2
#print axioms bound_pointStmt3
#print axioms bound_pointStmt4
#print axioms bound_pointStmt5
#print axioms bound_pointStmt6
#print axioms bound_pointStmt7
end SynergyHeightC.FragmentProofs
