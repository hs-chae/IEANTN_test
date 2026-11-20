import RamanujanPV.PackedSieveByteWidth
namespace RamanujanPV.PackedSieveByteControl1000
open PackedSieveKernel PackedSieveByteCount
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem raw_byte_result : byteCount 125 (primeBits 38358837684 1000) = 32 := by decide +kernel
#print axioms raw_byte_result
end RamanujanPV.PackedSieveByteControl1000
