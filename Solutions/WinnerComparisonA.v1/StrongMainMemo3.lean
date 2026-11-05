import StrongMemoProgram
namespace WinnerStrongOuter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
 theorem main3_memo_check : checkMainMemo (1/20) (1/2000) (1/20) (9236109/1000000000) 31900=true := by native_decide
 theorem cap3_memo_check : checkCapMemo (1/20) (1/2000) (1/20) 31900=true := by native_decide
 theorem main3_original_check : checkMain (1/20) (1/2000) (1/20) (9236109/1000000000) 31900=true := by
  rw [←checkMainMemo_eq]
  exact main3_memo_check
 theorem cap3_original_check : checkCap (1/20) (1/2000) (1/20) 31900=true := by
  rw [←checkCapMemo_eq]
  exact cap3_memo_check
#print axioms main3_original_check
#print axioms cap3_original_check
end WinnerStrongOuter
