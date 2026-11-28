import ForestTables
import ForestData02
import ForestData03
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
noncomputable section
namespace FapForest17
open RH080Next.FFT.IntegerModel
theorem layer03_checked : checkLayer w03 (out02.take 16384) (out02.drop 16384) out03=true := by
  decide +kernel
theorem layer03_trace : LayerTrace w03 (out02.take 16384) (out02.drop 16384) out03 := checkLayer_sound _ _ _ _ layer03_checked
#print axioms layer03_trace
end FapForest17
