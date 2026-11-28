import ForestTables
import ForestData04
import ForestData05
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
noncomputable section
namespace FapForest17
open RH080Next.FFT.IntegerModel
theorem layer05_checked : checkLayer w05 (out04.take 4096) (out04.drop 4096) out05=true := by
  decide +kernel
theorem layer05_trace : LayerTrace w05 (out04.take 4096) (out04.drop 4096) out05 := checkLayer_sound _ _ _ _ layer05_checked
#print axioms layer05_trace
end FapForest17
