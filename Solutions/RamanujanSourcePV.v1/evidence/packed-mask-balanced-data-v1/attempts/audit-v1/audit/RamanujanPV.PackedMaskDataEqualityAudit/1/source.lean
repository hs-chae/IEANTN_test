import RamanujanPV.PackedMaskDataEncoding.W256.Equality
import RamanujanPV.PackedMaskDataEncoding.W1024.Equality
import RamanujanPV.PackedMaskDataEncoding.W4096.Equality
import RamanujanPV.PackedMaskDataEncoding.W4096DataOnly.Equality
namespace RamanujanPV.PackedMaskDataEqualityAudit
example : PackedMaskDataEncoding.W256.value=PackedMaskDataEncoding.BaselineData.value := PackedMaskDataEncoding.W256.data_equal
example : PackedMaskDataEncoding.W1024.value=PackedMaskDataEncoding.BaselineData.value := PackedMaskDataEncoding.W1024.data_equal
example : PackedMaskDataEncoding.W4096.value=PackedMaskDataEncoding.BaselineData.value := PackedMaskDataEncoding.W4096.data_equal
example : PackedMaskDataEncoding.W4096DataOnly.value=PackedMaskDataEncoding.BaselineData.value := PackedMaskDataEncoding.W4096DataOnly.data_equal
#print axioms PackedMaskDataEncoding.W256.data_equal
#print axioms PackedMaskDataEncoding.W1024.data_equal
#print axioms PackedMaskDataEncoding.W4096.data_equal
#print axioms PackedMaskDataEncoding.W4096DataOnly.data_equal
end RamanujanPV.PackedMaskDataEqualityAudit
