import StrongWarmProgram
namespace WinnerStrongOuter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
 theorem warm0_check : checkWarm (1/10000) (9/1000000) (19286/10000000000) 100=true := by native_decide
#print axioms warm0_check
end WinnerStrongOuter
