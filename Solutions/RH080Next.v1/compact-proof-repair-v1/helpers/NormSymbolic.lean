import W4FFTPairedIntModel
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.PrivateNormProof
open RH080Next.FFT.IntegerModel
theorem normFromOutput_of_totals (n : Nat) (out : List CInt) (total quad : Nat)
    (hs : absSum out = total) (hq : W4.quad = quad) :
    W4.normFromOutput n out =
      ceilDiv (ceilDiv (ceilDiv total 1000000000000000000) 100) n +
      ceilDiv (ceilDiv (ceilDiv quad 3) n) n + 100 := by
  unfold W4.normFromOutput
  rw [fold_absSum, Nat.zero_add, hs, hq]

#print axioms normFromOutput_of_totals
end RH080Next.PrivateNormProof
