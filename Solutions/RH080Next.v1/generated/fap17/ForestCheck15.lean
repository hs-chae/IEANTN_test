import ForestTables
import ForestData14
import ForestData15
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
noncomputable section
namespace FapForest17
open RH080Next.FFT.IntegerModel
theorem layer15_checked : checkLayer w15 (out14.take 4) (out14.drop 4) out15=true := by
  decide +kernel
theorem layer15_trace : LayerTrace w15 (out14.take 4) (out14.drop 4) out15 := checkLayer_sound _ _ _ _ layer15_checked
#print axioms layer15_trace
end FapForest17
