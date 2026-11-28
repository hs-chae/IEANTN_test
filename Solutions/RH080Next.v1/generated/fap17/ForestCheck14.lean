import ForestTables
import ForestData13
import ForestData14
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
noncomputable section
namespace FapForest17
open RH080Next.FFT.IntegerModel
theorem layer14_checked : checkLayer w14 (out13.take 8) (out13.drop 8) out14=true := by
  decide +kernel
theorem layer14_trace : LayerTrace w14 (out13.take 8) (out13.drop 8) out14 := checkLayer_sound _ _ _ _ layer14_checked
#print axioms layer14_trace
end FapForest17
