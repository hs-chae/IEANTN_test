import ForestTables
import ForestData01
import ForestData02
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
noncomputable section
namespace FapForest17
open RH080Next.FFT.IntegerModel
theorem layer02_checked : checkLayer w02 (out01.take 32768) (out01.drop 32768) out02=true := by
  decide +kernel
theorem layer02_trace : LayerTrace w02 (out01.take 32768) (out01.drop 32768) out02 := checkLayer_sound _ _ _ _ layer02_checked
#print axioms layer02_trace
end FapForest17
