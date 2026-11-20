import RamanujanPV.PackedSievePrimitiveBits
import RamanujanPV.PackedMaskDataEncoding.W4096.Data
namespace RamanujanPV.PackedMaskDataEncoding.W4096
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem primitive_program_matches_data :
    PackedSievePrimitiveBits.primitiveBits 38358837684 1000000=value := by
  decide +kernel

theorem original_program_matches_data :
    PackedSieveKernel.primeBits 38358837684 1000000=value :=
  (PackedSievePrimitiveBits.primitiveBits_eq 38358837684 1000000).symm.trans primitive_program_matches_data
#print axioms primitive_program_matches_data
#print axioms original_program_matches_data
end RamanujanPV.PackedMaskDataEncoding.W4096
