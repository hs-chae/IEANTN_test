import ForestTables
import ForestData07
import ForestData08
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
noncomputable section
namespace FapForest17
open RH080Next.FFT.IntegerModel
theorem layer08_checked : checkLayer w08 (out07.take 512) (out07.drop 512) out08=true := by
  decide +kernel
theorem layer08_trace : LayerTrace w08 (out07.take 512) (out07.drop 512) out08 := checkLayer_sound _ _ _ _ layer08_checked
#print axioms layer08_trace
end FapForest17
