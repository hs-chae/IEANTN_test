import RamanujanPV.PackedMaskDataEncoding.BaselineData
import RamanujanPV.PackedMaskDataEncoding.W256.Data
namespace RamanujanPV.PackedMaskDataEncoding.W256
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem data_equal : value=RamanujanPV.PackedMaskDataEncoding.BaselineData.value := by decide +kernel
#print axioms data_equal
end RamanujanPV.PackedMaskDataEncoding.W256
