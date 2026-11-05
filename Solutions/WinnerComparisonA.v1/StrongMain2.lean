import StrongOuterProgram
namespace WinnerStrongOuter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
 theorem main2_check : checkMain (1/25) (1/2000) (9/200) (509117/10000000000) 20=true := by native_decide
 theorem cap2_check : checkCap (1/25) (1/2000) (9/200) 20=true := by native_decide
#print axioms main2_check
#print axioms cap2_check
end WinnerStrongOuter
