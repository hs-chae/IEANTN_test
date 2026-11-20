import RamanujanPV.PackedSieveKernel
namespace RamanujanPV.PackedSieveScout1000
open PackedSieveKernel
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem raw_swar_result : scoutCount 38358837684 1000 10 = 32 := by decide +kernel
#print axioms raw_swar_result
end RamanujanPV.PackedSieveScout1000
