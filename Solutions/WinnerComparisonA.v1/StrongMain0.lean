import StrongOuterProgram
namespace WinnerStrongOuter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
 theorem main0_check : checkMain (1/50) (1/2000) (7/200) (256908/10000000000) 10=true := by native_decide
 theorem cap0_check : checkCap (1/50) (1/2000) (7/200) 10=true := by native_decide
#print axioms main0_check
#print axioms cap0_check
end WinnerStrongOuter
