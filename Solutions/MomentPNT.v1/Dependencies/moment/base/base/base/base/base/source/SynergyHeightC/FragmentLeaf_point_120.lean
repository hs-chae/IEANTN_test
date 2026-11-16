import SynergyHeightC.FragmentData
import ScopedC.SourceBundle.FunctionTree
namespace SynergyHeightC.FragmentProofs
open ScopedC.Syntax ScopedC.SourceBundle
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false
def file_pointStmt120 : File := ⟨"function_pointHeight_stmt120.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt120.inc"⟩
def fragment_pointStmt120 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt120⟩
theorem bound_pointStmt120 : FunctionTree.LeafBound fragment_pointStmt120 file_pointStmt120 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt121 : File := ⟨"function_pointHeight_stmt121.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt121.inc"⟩
def fragment_pointStmt121 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt121⟩
theorem bound_pointStmt121 : FunctionTree.LeafBound fragment_pointStmt121 file_pointStmt121 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt122 : File := ⟨"function_pointHeight_stmt122.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt122.inc"⟩
def fragment_pointStmt122 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt122⟩
theorem bound_pointStmt122 : FunctionTree.LeafBound fragment_pointStmt122 file_pointStmt122 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt123 : File := ⟨"function_pointHeight_stmt123.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt123.inc"⟩
def fragment_pointStmt123 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt123⟩
theorem bound_pointStmt123 : FunctionTree.LeafBound fragment_pointStmt123 file_pointStmt123 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt124 : File := ⟨"function_pointHeight_stmt124.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt124.inc"⟩
def fragment_pointStmt124 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt124⟩
theorem bound_pointStmt124 : FunctionTree.LeafBound fragment_pointStmt124 file_pointStmt124 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt125 : File := ⟨"function_pointHeight_stmt125.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt125.inc"⟩
def fragment_pointStmt125 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt125⟩
theorem bound_pointStmt125 : FunctionTree.LeafBound fragment_pointStmt125 file_pointStmt125 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt126 : File := ⟨"function_pointHeight_stmt126.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt126.inc"⟩
def fragment_pointStmt126 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt126⟩
theorem bound_pointStmt126 : FunctionTree.LeafBound fragment_pointStmt126 file_pointStmt126 := by unfold FunctionTree.LeafBound; decide +kernel
def file_pointStmt127 : File := ⟨"function_pointHeight_stmt127.inc",include_str "../../height-bundle-source-v3/function_pointHeight_stmt127.inc"⟩
def fragment_pointStmt127 : FunctionTree.StatementFragment := ⟨FragmentData.pointStmt127⟩
theorem bound_pointStmt127 : FunctionTree.LeafBound fragment_pointStmt127 file_pointStmt127 := by unfold FunctionTree.LeafBound; decide +kernel
#print axioms bound_pointStmt120
#print axioms bound_pointStmt121
#print axioms bound_pointStmt122
#print axioms bound_pointStmt123
#print axioms bound_pointStmt124
#print axioms bound_pointStmt125
#print axioms bound_pointStmt126
#print axioms bound_pointStmt127
end SynergyHeightC.FragmentProofs
