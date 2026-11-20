/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.PrimeBaseMaskScout.BaseP
import RamanujanPV.PackedSievePrimitiveMaskMillion
namespace RamanujanPV.PrimeBaseMaskScout.MainP
open PackedSievePrimeBase
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
/-- Independent kernel computation of the new algorithm against the SAME old
proposed hexadecimal data. No old mask-correctness theorem is used. -/
theorem primitive_evaluated : primitiveFromList 38358837684 1000000 BaseP.primes =
    PackedSievePrimitiveMaskMillion.bits := by decide +kernel
/-- The new computed output agrees with the old mathematical primeBits. The
prime-list premise is CLOSED by the separately computed canonical base. -/
theorem original_mask_equality : PackedSieveKernel.primeBits 38358837684 1000000 =
    PackedSievePrimitiveMaskMillion.bits :=
  (primitive_eq_original BaseP.full_P_certificate (by decide)).symm.trans primitive_evaluated
#print axioms primitive_evaluated
#print axioms original_mask_equality
end RamanujanPV.PrimeBaseMaskScout.MainP
