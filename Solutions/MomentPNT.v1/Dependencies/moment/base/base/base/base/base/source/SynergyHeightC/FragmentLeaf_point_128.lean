import SynergyHeightC.FragmentData
import ScopedC.SourceBundle.FunctionTree
namespace SynergyHeightC.FragmentProofs
open ScopedC.Syntax ScopedC.SourceBundle
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false
def file_pointStmt128 : File := ⟨"function_pointHeight_stmt128.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt128.inc"⟩
def fragment_pointStmt128 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt128⟩
theorem bound_pointStmt128 : FunctionTree.LeafBound fragment_pointStmt128 file_pointStmt128 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt129 : File := ⟨"function_pointHeight_stmt129.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt129.inc"⟩
def fragment_pointStmt129 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt129⟩
theorem bound_pointStmt129 : FunctionTree.LeafBound fragment_pointStmt129 file_pointStmt129 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt130 : File := ⟨"function_pointHeight_stmt130.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt130.inc"⟩
def fragment_pointStmt130 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt130⟩
theorem bound_pointStmt130 : FunctionTree.LeafBound fragment_pointStmt130 file_pointStmt130 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt131 : File := ⟨"function_pointHeight_stmt131.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt131.inc"⟩
def fragment_pointStmt131 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt131⟩
theorem bound_pointStmt131 : FunctionTree.LeafBound fragment_pointStmt131 file_pointStmt131 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt132 : File := ⟨"function_pointHeight_stmt132.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt132.inc"⟩
def fragment_pointStmt132 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt132⟩
theorem bound_pointStmt132 : FunctionTree.LeafBound fragment_pointStmt132 file_pointStmt132 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt133 : File := ⟨"function_pointHeight_stmt133.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt133.inc"⟩
def fragment_pointStmt133 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt133⟩
theorem bound_pointStmt133 : FunctionTree.LeafBound fragment_pointStmt133 file_pointStmt133 := by unfold FunctionTree.LeafBound; decide +kernel
#print axioms bound_pointStmt128
#print axioms bound_pointStmt129
#print axioms bound_pointStmt130
#print axioms bound_pointStmt131
#print axioms bound_pointStmt132
#print axioms bound_pointStmt133
end SynergyHeightC.FragmentProofs
