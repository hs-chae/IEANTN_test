import ForestTables
import ForestData03
import ForestData04
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
noncomputable section
namespace FapForest17
open RH080Next.FFT.IntegerModel
theorem layer04_checked : checkLayer w04 (out03.take 8192) (out03.drop 8192) out04=true := by
  decide +kernel
theorem layer04_trace : LayerTrace w04 (out03.take 8192) (out03.drop 8192) out04 := checkLayer_sound _ _ _ _ layer04_checked
#print axioms layer04_trace
end FapForest17
