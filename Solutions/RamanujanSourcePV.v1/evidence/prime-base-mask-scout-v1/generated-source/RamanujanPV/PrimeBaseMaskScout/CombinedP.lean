/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.PrimeBaseMaskScout.BaseP
import RamanujanPV.PackedMaskDataEncoding.W4096DataOnly.Data
namespace RamanujanPV.PrimeBaseMaskScout.CombinedP
open PackedSievePrimeBase
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
/-- Independent kernel execution against standalone balanced4096-bit DATA.
No baseline full-mask DATA, old mask proof or calibration theorem is imported. -/
theorem primitive_evaluated : primitiveFromList 38358837684 1000000 BaseP.primes =
    PackedMaskDataEncoding.W4096DataOnly.value := by decide +kernel
/-- All prime-list correctness premises are closed by canonical base computation. -/
theorem original_mask_equality : PackedSieveKernel.primeBits 38358837684 1000000 =
    PackedMaskDataEncoding.W4096DataOnly.value :=
  (primitive_eq_original BaseP.full_P_certificate (by decide)).symm.trans primitive_evaluated
#print axioms primitive_evaluated
#print axioms original_mask_equality
end RamanujanPV.PrimeBaseMaskScout.CombinedP
