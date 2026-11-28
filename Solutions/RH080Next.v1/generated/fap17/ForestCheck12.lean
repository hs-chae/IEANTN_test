import ForestTables
import ForestData11
import ForestData12
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
noncomputable section
namespace FapForest17
open RH080Next.FFT.IntegerModel
theorem layer12_checked : checkLayer w12 (out11.take 32) (out11.drop 32) out12=true := by
  decide +kernel
theorem layer12_trace : LayerTrace w12 (out11.take 32) (out11.drop 32) out12 := checkLayer_sound _ _ _ _ layer12_checked
#print axioms layer12_trace
end FapForest17
