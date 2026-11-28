import ForestTables
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
noncomputable section
namespace FapForest17
open RH080Next.FFT.IntegerModel
theorem twiddles_checked : checkTwiddles seed (unit,0) w17.tail=true := by decide +kernel
theorem global_twiddle_trace : TwiddleTrace seed (unit,0) w17.tail := checkTwiddles_sound _ _ _ twiddles_checked
theorem decimation01 : EvenTrace w02 w01 := checkEvens_sound _ _ (by decide +kernel)
theorem decimation02 : EvenTrace w03 w02 := checkEvens_sound _ _ (by decide +kernel)
theorem decimation03 : EvenTrace w04 w03 := checkEvens_sound _ _ (by decide +kernel)
theorem decimation04 : EvenTrace w05 w04 := checkEvens_sound _ _ (by decide +kernel)
theorem decimation05 : EvenTrace w06 w05 := checkEvens_sound _ _ (by decide +kernel)
theorem decimation06 : EvenTrace w07 w06 := checkEvens_sound _ _ (by decide +kernel)
theorem decimation07 : EvenTrace w08 w07 := checkEvens_sound _ _ (by decide +kernel)
theorem decimation08 : EvenTrace w09 w08 := checkEvens_sound _ _ (by decide +kernel)
theorem decimation09 : EvenTrace w10 w09 := checkEvens_sound _ _ (by decide +kernel)
theorem decimation10 : EvenTrace w11 w10 := checkEvens_sound _ _ (by decide +kernel)
theorem decimation11 : EvenTrace w12 w11 := checkEvens_sound _ _ (by decide +kernel)
theorem decimation12 : EvenTrace w13 w12 := checkEvens_sound _ _ (by decide +kernel)
theorem decimation13 : EvenTrace w14 w13 := checkEvens_sound _ _ (by decide +kernel)
theorem decimation14 : EvenTrace w15 w14 := checkEvens_sound _ _ (by decide +kernel)
theorem decimation15 : EvenTrace w16 w15 := checkEvens_sound _ _ (by decide +kernel)
theorem decimation16 : EvenTrace w17 w16 := checkEvens_sound _ _ (by decide +kernel)
#print axioms global_twiddle_trace
#print axioms decimation01
#print axioms decimation02
#print axioms decimation03
#print axioms decimation04
#print axioms decimation05
#print axioms decimation06
#print axioms decimation07
#print axioms decimation08
#print axioms decimation09
#print axioms decimation10
#print axioms decimation11
#print axioms decimation12
#print axioms decimation13
#print axioms decimation14
#print axioms decimation15
#print axioms decimation16
end FapForest17
