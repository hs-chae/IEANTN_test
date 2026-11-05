import StrongWarmProgram
namespace WinnerStrongOuter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
 theorem warm1_check : checkWarm (1/1000) (9/100000) (441466/10000000000) 100=true := by native_decide
#print axioms warm1_check
end WinnerStrongOuter
