import ForestTables
import ForestData08
import ForestData09
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
noncomputable section
namespace FapForest17
open RH080Next.FFT.IntegerModel
theorem layer09_checked : checkLayer w09 (out08.take 256) (out08.drop 256) out09=true := by
  decide +kernel
theorem layer09_trace : LayerTrace w09 (out08.take 256) (out08.drop 256) out09 := checkLayer_sound _ _ _ _ layer09_checked
#print axioms layer09_trace
end FapForest17
