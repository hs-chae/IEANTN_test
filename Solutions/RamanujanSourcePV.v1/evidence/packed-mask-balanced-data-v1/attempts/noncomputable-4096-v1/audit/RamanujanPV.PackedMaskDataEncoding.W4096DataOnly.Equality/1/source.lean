import RamanujanPV.PackedMaskDataEncoding.BaselineData
import RamanujanPV.PackedMaskDataEncoding.W4096DataOnly.Data
namespace RamanujanPV.PackedMaskDataEncoding.W4096DataOnly
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem data_equal : value=PackedMaskDataEncoding.BaselineData.value := by decide +kernel
#print axioms data_equal
end RamanujanPV.PackedMaskDataEncoding.W4096DataOnly
