import ForestTables
import ForestData10
import ForestData11
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
noncomputable section
namespace FapForest17
open RH080Next.FFT.IntegerModel
theorem layer11_checked : checkLayer w11 (out10.take 64) (out10.drop 64) out11=true := by
  decide +kernel
theorem layer11_trace : LayerTrace w11 (out10.take 64) (out10.drop 64) out11 := checkLayer_sound _ _ _ _ layer11_checked
#print axioms layer11_trace
end FapForest17
