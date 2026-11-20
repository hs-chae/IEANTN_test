/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.PackedSievePrimitiveMaskMillion
namespace RamanujanPV.PrimeBaseMaskScout.OldControlP
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
/-- Fresh same-host control: recompute the original prime-filtered algorithm,
using only the same proposed hexadecimal literal, never the old equality proof. -/
theorem primitive_evaluated : PackedSievePrimitiveBits.primitiveBits 38358837684 1000000 =
    PackedSievePrimitiveMaskMillion.bits := by decide +kernel
#print axioms primitive_evaluated
end RamanujanPV.PrimeBaseMaskScout.OldControlP
