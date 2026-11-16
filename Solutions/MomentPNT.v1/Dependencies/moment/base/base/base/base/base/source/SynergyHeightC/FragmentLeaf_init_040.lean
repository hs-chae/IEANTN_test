import SynergyHeightC.FragmentData
import ScopedC.SourceBundle.FunctionTree
namespace SynergyHeightC.FragmentProofs
open ScopedC.Syntax ScopedC.SourceBundle
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false
def file_initStmt40 : File := ⟨"function_initializePointConstants_stmt040.inc",include_str "../../height-bundle-source-v3/function_initializePointConstants_stmt040.inc"⟩
def fragment_initStmt40 : FunctionTree.StatementFragment := ⟨FragmentData.initStmt40⟩
theorem bound_initStmt40 : FunctionTree.LeafBound fragment_initStmt40 file_initStmt40 := by unfold FunctionTree.LeafBound; decide +kernel
def file_initStmt41 : File := ⟨"function_initializePointConstants_stmt041.inc",include_str "../../height-bundle-source-v3/function_initializePointConstants_stmt041.inc"⟩
def fragment_initStmt41 : FunctionTree.StatementFragment := ⟨FragmentData.initStmt41⟩
theorem bound_initStmt41 : FunctionTree.LeafBound fragment_initStmt41 file_initStmt41 := by unfold FunctionTree.LeafBound; decide +kernel
def file_initStmt42 : File := ⟨"function_initializePointConstants_stmt042.inc",include_str "../../height-bundle-source-v3/function_initializePointConstants_stmt042.inc"⟩
def fragment_initStmt42 : FunctionTree.StatementFragment := ⟨FragmentData.initStmt42⟩
theorem bound_initStmt42 : FunctionTree.LeafBound fragment_initStmt42 file_initStmt42 := by unfold FunctionTree.LeafBound; decide +kernel
def file_initStmt43 : File := ⟨"function_initializePointConstants_stmt043.inc",include_str "../../height-bundle-source-v3/function_initializePointConstants_stmt043.inc"⟩
def fragment_initStmt43 : FunctionTree.StatementFragment := ⟨FragmentData.initStmt43⟩
theorem bound_initStmt43 : FunctionTree.LeafBound fragment_initStmt43 file_initStmt43 := by unfold FunctionTree.LeafBound; decide +kernel
def file_initStmt44 : File := ⟨"function_initializePointConstants_stmt044.inc",include_str "../../height-bundle-source-v3/function_initializePointConstants_stmt044.inc"⟩
def fragment_initStmt44 : FunctionTree.StatementFragment := ⟨FragmentData.initStmt44⟩
theorem bound_initStmt44 : FunctionTree.LeafBound fragment_initStmt44 file_initStmt44 := by unfold FunctionTree.LeafBound; decide +kernel
def file_initStmt45 : File := ⟨"function_initializePointConstants_stmt045.inc",include_str "../../height-bundle-source-v3/function_initializePointConstants_stmt045.inc"⟩
def fragment_initStmt45 : FunctionTree.StatementFragment := ⟨FragmentData.initStmt45⟩
theorem bound_initStmt45 : FunctionTree.LeafBound fragment_initStmt45 file_initStmt45 := by unfold FunctionTree.LeafBound; decide +kernel
def file_initStmt46 : File := ⟨"function_initializePointConstants_stmt046.inc",include_str "../../height-bundle-source-v3/function_initializePointConstants_stmt046.inc"⟩
def fragment_initStmt46 : FunctionTree.StatementFragment := ⟨FragmentData.initStmt46⟩
theorem bound_initStmt46 : FunctionTree.LeafBound fragment_initStmt46 file_initStmt46 := by unfold FunctionTree.LeafBound; decide +kernel
def file_initStmt47 : File := ⟨"function_initializePointConstants_stmt047.inc",include_str "../../height-bundle-source-v3/function_initializePointConstants_stmt047.inc"⟩
def fragment_initStmt47 : FunctionTree.StatementFragment := ⟨FragmentData.initStmt47⟩
theorem bound_initStmt47 : FunctionTree.LeafBound fragment_initStmt47 file_initStmt47 := by unfold FunctionTree.LeafBound; decide +kernel
#print axioms bound_initStmt40
#print axioms bound_initStmt41
#print axioms bound_initStmt42
#print axioms bound_initStmt43
#print axioms bound_initStmt44
#print axioms bound_initStmt45
#print axioms bound_initStmt46
#print axioms bound_initStmt47
end SynergyHeightC.FragmentProofs
