import SynergyHeightC.FragmentData
import ScopedC.SourceBundle.FunctionTree
namespace SynergyHeightC.FragmentProofs
open ScopedC.Syntax ScopedC.SourceBundle
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false
def file_pointStmt88 : File := ⟨"function_pointHeight_stmt088.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt088.inc"⟩
def fragment_pointStmt88 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt88⟩
theorem bound_pointStmt88 : FunctionTree.LeafBound fragment_pointStmt88 file_pointStmt88 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt89 : File := ⟨"function_pointHeight_stmt089.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt089.inc"⟩
def fragment_pointStmt89 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt89⟩
theorem bound_pointStmt89 : FunctionTree.LeafBound fragment_pointStmt89 file_pointStmt89 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt90 : File := ⟨"function_pointHeight_stmt090.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt090.inc"⟩
def fragment_pointStmt90 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt90⟩
theorem bound_pointStmt90 : FunctionTree.LeafBound fragment_pointStmt90 file_pointStmt90 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt91 : File := ⟨"function_pointHeight_stmt091.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt091.inc"⟩
def fragment_pointStmt91 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt91⟩
theorem bound_pointStmt91 : FunctionTree.LeafBound fragment_pointStmt91 file_pointStmt91 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt92 : File := ⟨"function_pointHeight_stmt092.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt092.inc"⟩
def fragment_pointStmt92 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt92⟩
theorem bound_pointStmt92 : FunctionTree.LeafBound fragment_pointStmt92 file_pointStmt92 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt93 : File := ⟨"function_pointHeight_stmt093.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt093.inc"⟩
def fragment_pointStmt93 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt93⟩
theorem bound_pointStmt93 : FunctionTree.LeafBound fragment_pointStmt93 file_pointStmt93 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt94 : File := ⟨"function_pointHeight_stmt094.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt094.inc"⟩
def fragment_pointStmt94 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt94⟩
theorem bound_pointStmt94 : FunctionTree.LeafBound fragment_pointStmt94 file_pointStmt94 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt95 : File := ⟨"function_pointHeight_stmt095.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt095.inc"⟩
def fragment_pointStmt95 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt95⟩
theorem bound_pointStmt95 : FunctionTree.LeafBound fragment_pointStmt95 file_pointStmt95 := by unfold FunctionTree.LeafBound; decide +kernel
#print axioms bound_pointStmt88
#print axioms bound_pointStmt89
#print axioms bound_pointStmt90
#print axioms bound_pointStmt91
#print axioms bound_pointStmt92
#print axioms bound_pointStmt93
#print axioms bound_pointStmt94
#print axioms bound_pointStmt95
end SynergyHeightC.FragmentProofs
