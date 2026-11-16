import SynergyHeightC.FragmentData
import ScopedC.SourceBundle.FunctionTree
namespace SynergyHeightC.FragmentProofs
open ScopedC.Syntax ScopedC.SourceBundle
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false
def file_pointStmt16 : File := ⟨"function_pointHeight_stmt016.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt016.inc"⟩
def fragment_pointStmt16 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt16⟩
theorem bound_pointStmt16 : FunctionTree.LeafBound fragment_pointStmt16 file_pointStmt16 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt17 : File := ⟨"function_pointHeight_stmt017.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt017.inc"⟩
def fragment_pointStmt17 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt17⟩
theorem bound_pointStmt17 : FunctionTree.LeafBound fragment_pointStmt17 file_pointStmt17 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt18 : File := ⟨"function_pointHeight_stmt018.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt018.inc"⟩
def fragment_pointStmt18 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt18⟩
theorem bound_pointStmt18 : FunctionTree.LeafBound fragment_pointStmt18 file_pointStmt18 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt19 : File := ⟨"function_pointHeight_stmt019.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt019.inc"⟩
def fragment_pointStmt19 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt19⟩
theorem bound_pointStmt19 : FunctionTree.LeafBound fragment_pointStmt19 file_pointStmt19 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt20 : File := ⟨"function_pointHeight_stmt020.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt020.inc"⟩
def fragment_pointStmt20 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt20⟩
theorem bound_pointStmt20 : FunctionTree.LeafBound fragment_pointStmt20 file_pointStmt20 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt21 : File := ⟨"function_pointHeight_stmt021.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt021.inc"⟩
def fragment_pointStmt21 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt21⟩
theorem bound_pointStmt21 : FunctionTree.LeafBound fragment_pointStmt21 file_pointStmt21 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt22 : File := ⟨"function_pointHeight_stmt022.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt022.inc"⟩
def fragment_pointStmt22 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt22⟩
theorem bound_pointStmt22 : FunctionTree.LeafBound fragment_pointStmt22 file_pointStmt22 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt23 : File := ⟨"function_pointHeight_stmt023.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt023.inc"⟩
def fragment_pointStmt23 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt23⟩
theorem bound_pointStmt23 : FunctionTree.LeafBound fragment_pointStmt23 file_pointStmt23 := by unfold FunctionTree.LeafBound; decide +kernel
#print axioms bound_pointStmt16
#print axioms bound_pointStmt17
#print axioms bound_pointStmt18
#print axioms bound_pointStmt19
#print axioms bound_pointStmt20
#print axioms bound_pointStmt21
#print axioms bound_pointStmt22
#print axioms bound_pointStmt23
end SynergyHeightC.FragmentProofs
