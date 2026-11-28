import ForestTables
import ForestData05
import ForestData06
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
noncomputable section
namespace FapForest17
open RH080Next.FFT.IntegerModel
theorem layer06_checked : checkLayer w06 (out05.take 2048) (out05.drop 2048) out06=true := by
  decide +kernel
theorem layer06_trace : LayerTrace w06 (out05.take 2048) (out05.drop 2048) out06 := checkLayer_sound _ _ _ _ layer06_checked
#print axioms layer06_trace
end FapForest17
