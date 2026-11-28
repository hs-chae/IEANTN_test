import ForestTables
import ForestData16
import ForestData17
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
noncomputable section
namespace FapForest17
open RH080Next.FFT.IntegerModel
theorem layer17_checked : checkLayer w17 (out16.take 1) (out16.drop 1) out17=true := by
  decide +kernel
theorem layer17_trace : LayerTrace w17 (out16.take 1) (out16.drop 1) out17 := checkLayer_sound _ _ _ _ layer17_checked
#print axioms layer17_trace
end FapForest17
