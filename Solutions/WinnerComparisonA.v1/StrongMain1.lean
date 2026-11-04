import StrongOuterProgram
namespace WinnerStrongOuter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
 theorem main1_check : checkMain (1/40) (1/2000) (1/25) (767989/10000000000) 30=true := by native_decide
 theorem cap1_check : checkCap (1/40) (1/2000) (1/25) 30=true := by native_decide
#print axioms main1_check
#print axioms cap1_check
end WinnerStrongOuter
