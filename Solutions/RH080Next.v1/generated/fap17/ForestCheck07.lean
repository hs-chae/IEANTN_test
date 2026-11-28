import ForestTables
import ForestData06
import ForestData07
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
noncomputable section
namespace FapForest17
open RH080Next.FFT.IntegerModel
theorem layer07_checked : checkLayer w07 (out06.take 1024) (out06.drop 1024) out07=true := by
  decide +kernel
theorem layer07_trace : LayerTrace w07 (out06.take 1024) (out06.drop 1024) out07 := checkLayer_sound _ _ _ _ layer07_checked
#print axioms layer07_trace
end FapForest17
