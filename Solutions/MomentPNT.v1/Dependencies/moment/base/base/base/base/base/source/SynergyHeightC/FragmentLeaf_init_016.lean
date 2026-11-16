import SynergyHeightC.FragmentData
import ScopedC.SourceBundle.FunctionTree
namespace SynergyHeightC.FragmentProofs
open ScopedC.Syntax ScopedC.SourceBundle
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false
def file_initStmt16 : File := ⟨"function_initializePointConstants_stmt016.inc",include_str "../../height-bundle-source-v3/function_initializePointConstants_stmt016.inc"⟩
def fragment_initStmt16 : FunctionTree.StatementFragment := ⟨FragmentData.initStmt16⟩
theorem bound_initStmt16 : FunctionTree.LeafBound fragment_initStmt16 file_initStmt16 := by unfold FunctionTree.LeafBound; decide +kernel
def file_initStmt17 : File := ⟨"function_initializePointConstants_stmt017.inc",include_str "../../height-bundle-source-v3/function_initializePointConstants_stmt017.inc"⟩
def fragment_initStmt17 : FunctionTree.StatementFragment := ⟨FragmentData.initStmt17⟩
theorem bound_initStmt17 : FunctionTree.LeafBound fragment_initStmt17 file_initStmt17 := by unfold FunctionTree.LeafBound; decide +kernel
def file_initStmt18 : File := ⟨"function_initializePointConstants_stmt018.inc",include_str "../../height-bundle-source-v3/function_initializePointConstants_stmt018.inc"⟩
def fragment_initStmt18 : FunctionTree.StatementFragment := ⟨FragmentData.initStmt18⟩
theorem bound_initStmt18 : FunctionTree.LeafBound fragment_initStmt18 file_initStmt18 := by unfold FunctionTree.LeafBound; decide +kernel
def file_initStmt19 : File := ⟨"function_initializePointConstants_stmt019.inc",include_str "../../height-bundle-source-v3/function_initializePointConstants_stmt019.inc"⟩
def fragment_initStmt19 : FunctionTree.StatementFragment := ⟨FragmentData.initStmt19⟩
theorem bound_initStmt19 : FunctionTree.LeafBound fragment_initStmt19 file_initStmt19 := by unfold FunctionTree.LeafBound; decide +kernel
def file_initStmt20 : File := ⟨"function_initializePointConstants_stmt020.inc",include_str "../../height-bundle-source-v3/function_initializePointConstants_stmt020.inc"⟩
def fragment_initStmt20 : FunctionTree.StatementFragment := ⟨FragmentData.initStmt20⟩
theorem bound_initStmt20 : FunctionTree.LeafBound fragment_initStmt20 file_initStmt20 := by unfold FunctionTree.LeafBound; decide +kernel
def file_initStmt21 : File := ⟨"function_initializePointConstants_stmt021.inc",include_str "../../height-bundle-source-v3/function_initializePointConstants_stmt021.inc"⟩
def fragment_initStmt21 : FunctionTree.StatementFragment := ⟨FragmentData.initStmt21⟩
theorem bound_initStmt21 : FunctionTree.LeafBound fragment_initStmt21 file_initStmt21 := by unfold FunctionTree.LeafBound; decide +kernel
def file_initStmt22 : File := ⟨"function_initializePointConstants_stmt022.inc",include_str "../../height-bundle-source-v3/function_initializePointConstants_stmt022.inc"⟩
def fragment_initStmt22 : FunctionTree.StatementFragment := ⟨FragmentData.initStmt22⟩
theorem bound_initStmt22 : FunctionTree.LeafBound fragment_initStmt22 file_initStmt22 := by unfold FunctionTree.LeafBound; decide +kernel
def file_initStmt23 : File := ⟨"function_initializePointConstants_stmt023.inc",include_str "../../height-bundle-source-v3/function_initializePointConstants_stmt023.inc"⟩
def fragment_initStmt23 : FunctionTree.StatementFragment := ⟨FragmentData.initStmt23⟩
theorem bound_initStmt23 : FunctionTree.LeafBound fragment_initStmt23 file_initStmt23 := by unfold FunctionTree.LeafBound; decide +kernel
#print axioms bound_initStmt16
#print axioms bound_initStmt17
#print axioms bound_initStmt18
#print axioms bound_initStmt19
#print axioms bound_initStmt20
#print axioms bound_initStmt21
#print axioms bound_initStmt22
#print axioms bound_initStmt23
end SynergyHeightC.FragmentProofs
