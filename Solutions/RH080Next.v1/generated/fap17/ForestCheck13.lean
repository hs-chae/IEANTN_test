import ForestTables
import ForestData12
import ForestData13
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
noncomputable section
namespace FapForest17
open RH080Next.FFT.IntegerModel
theorem layer13_checked : checkLayer w13 (out12.take 16) (out12.drop 16) out13=true := by
  decide +kernel
theorem layer13_trace : LayerTrace w13 (out12.take 16) (out12.drop 16) out13 := checkLayer_sound _ _ _ _ layer13_checked
#print axioms layer13_trace
end FapForest17
