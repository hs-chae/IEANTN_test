import ForestTables
import ForestData15
import ForestData16
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
noncomputable section
namespace FapForest17
open RH080Next.FFT.IntegerModel
theorem layer16_checked : checkLayer w16 (out15.take 2) (out15.drop 2) out16=true := by
  decide +kernel
theorem layer16_trace : LayerTrace w16 (out15.take 2) (out15.drop 2) out16 := checkLayer_sound _ _ _ _ layer16_checked
#print axioms layer16_trace
end FapForest17
