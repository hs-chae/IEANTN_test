import ForestTables
import ForestData09
import ForestData10
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
noncomputable section
namespace FapForest17
open RH080Next.FFT.IntegerModel
theorem layer10_checked : checkLayer w10 (out09.take 128) (out09.drop 128) out10=true := by
  decide +kernel
theorem layer10_trace : LayerTrace w10 (out09.take 128) (out09.drop 128) out10 := checkLayer_sound _ _ _ _ layer10_checked
#print axioms layer10_trace
end FapForest17
