import SynergyHeightC.FragmentData
import ScopedC.SourceBundle.FunctionTree
namespace SynergyHeightC.FragmentProofs
open ScopedC.Syntax ScopedC.SourceBundle
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false
def file_pointStmt40 : File := ⟨"function_pointHeight_stmt040.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt040.inc"⟩
def fragment_pointStmt40 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt40⟩
theorem bound_pointStmt40 : FunctionTree.LeafBound fragment_pointStmt40 file_pointStmt40 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt41 : File := ⟨"function_pointHeight_stmt041.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt041.inc"⟩
def fragment_pointStmt41 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt41⟩
theorem bound_pointStmt41 : FunctionTree.LeafBound fragment_pointStmt41 file_pointStmt41 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt42 : File := ⟨"function_pointHeight_stmt042.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt042.inc"⟩
def fragment_pointStmt42 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt42⟩
theorem bound_pointStmt42 : FunctionTree.LeafBound fragment_pointStmt42 file_pointStmt42 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt43 : File := ⟨"function_pointHeight_stmt043.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt043.inc"⟩
def fragment_pointStmt43 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt43⟩
theorem bound_pointStmt43 : FunctionTree.LeafBound fragment_pointStmt43 file_pointStmt43 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt44 : File := ⟨"function_pointHeight_stmt044.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt044.inc"⟩
def fragment_pointStmt44 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt44⟩
theorem bound_pointStmt44 : FunctionTree.LeafBound fragment_pointStmt44 file_pointStmt44 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt45 : File := ⟨"function_pointHeight_stmt045.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt045.inc"⟩
def fragment_pointStmt45 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt45⟩
theorem bound_pointStmt45 : FunctionTree.LeafBound fragment_pointStmt45 file_pointStmt45 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt46 : File := ⟨"function_pointHeight_stmt046.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt046.inc"⟩
def fragment_pointStmt46 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt46⟩
theorem bound_pointStmt46 : FunctionTree.LeafBound fragment_pointStmt46 file_pointStmt46 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt47 : File := ⟨"function_pointHeight_stmt047.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt047.inc"⟩
def fragment_pointStmt47 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt47⟩
theorem bound_pointStmt47 : FunctionTree.LeafBound fragment_pointStmt47 file_pointStmt47 := by unfold FunctionTree.LeafBound; decide +kernel
#print axioms bound_pointStmt40
#print axioms bound_pointStmt41
#print axioms bound_pointStmt42
#print axioms bound_pointStmt43
#print axioms bound_pointStmt44
#print axioms bound_pointStmt45
#print axioms bound_pointStmt46
#print axioms bound_pointStmt47
end SynergyHeightC.FragmentProofs
