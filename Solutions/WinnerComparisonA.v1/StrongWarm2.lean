import StrongWarmProgram
namespace WinnerStrongOuter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
 theorem warm2_check : checkWarm (1/100) (1/10000) (510932/10000000000) 100=true := by native_decide
#print axioms warm2_check
end WinnerStrongOuter
