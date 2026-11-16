import SynergyHeightC.FragmentData
import ScopedC.SourceBundle.FunctionTree
namespace SynergyHeightC.FragmentProofs
open ScopedC.Syntax ScopedC.SourceBundle
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false
def file_pointStmt72 : File := ⟨"function_pointHeight_stmt072.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt072.inc"⟩
def fragment_pointStmt72 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt72⟩
theorem bound_pointStmt72 : FunctionTree.LeafBound fragment_pointStmt72 file_pointStmt72 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt73 : File := ⟨"function_pointHeight_stmt073.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt073.inc"⟩
def fragment_pointStmt73 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt73⟩
theorem bound_pointStmt73 : FunctionTree.LeafBound fragment_pointStmt73 file_pointStmt73 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt74 : File := ⟨"function_pointHeight_stmt074.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt074.inc"⟩
def fragment_pointStmt74 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt74⟩
theorem bound_pointStmt74 : FunctionTree.LeafBound fragment_pointStmt74 file_pointStmt74 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt75 : File := ⟨"function_pointHeight_stmt075.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt075.inc"⟩
def fragment_pointStmt75 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt75⟩
theorem bound_pointStmt75 : FunctionTree.LeafBound fragment_pointStmt75 file_pointStmt75 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt76 : File := ⟨"function_pointHeight_stmt076.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt076.inc"⟩
def fragment_pointStmt76 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt76⟩
theorem bound_pointStmt76 : FunctionTree.LeafBound fragment_pointStmt76 file_pointStmt76 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt77 : File := ⟨"function_pointHeight_stmt077.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt077.inc"⟩
def fragment_pointStmt77 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt77⟩
theorem bound_pointStmt77 : FunctionTree.LeafBound fragment_pointStmt77 file_pointStmt77 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt78 : File := ⟨"function_pointHeight_stmt078.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt078.inc"⟩
def fragment_pointStmt78 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt78⟩
theorem bound_pointStmt78 : FunctionTree.LeafBound fragment_pointStmt78 file_pointStmt78 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt79 : File := ⟨"function_pointHeight_stmt079.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt079.inc"⟩
def fragment_pointStmt79 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt79⟩
theorem bound_pointStmt79 : FunctionTree.LeafBound fragment_pointStmt79 file_pointStmt79 := by unfold FunctionTree.LeafBound; decide +kernel
#print axioms bound_pointStmt72
#print axioms bound_pointStmt73
#print axioms bound_pointStmt74
#print axioms bound_pointStmt75
#print axioms bound_pointStmt76
#print axioms bound_pointStmt77
#print axioms bound_pointStmt78
#print axioms bound_pointStmt79
end SynergyHeightC.FragmentProofs
