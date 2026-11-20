import RamanujanPV.PackedSieveByteWidth
namespace RamanujanPV.PackedSieveByteBlock0000
open PackedSieveKernel PackedSieveByteCount
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem raw_byte_result : byteCount 8192 (primeBits 38358837684 65536) = 2664 := by decide +kernel
#print axioms raw_byte_result
end RamanujanPV.PackedSieveByteBlock0000
