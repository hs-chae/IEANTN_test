import ForestTables
import ForestData01
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
noncomputable section
namespace FapForest17
open RH080Next.FFT.IntegerModel
theorem layer01_checked : checkLayer w01 (leaves.take 65536) (leaves.drop 65536) out01=true := by
  decide +kernel
theorem layer01_trace : LayerTrace w01 (leaves.take 65536) (leaves.drop 65536) out01 := checkLayer_sound _ _ _ _ layer01_checked
#print axioms layer01_trace
end FapForest17
