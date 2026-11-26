/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTComplexModel
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option Elab.async false
namespace RH080Next.FFTPV.ComplexSource
open FFT.Limbs

/-- Euclidean division can round a negative signed value away from zero by
one unit. This generic integer lemma covers that branch explicitly. -/
theorem quotient_natAbs_le (z : Int) (denominator cap : Nat) (small : z.natAbs≤cap) :
    (z/(denominator:Nat)).natAbs≤cap/denominator+1:=by
  rw [Int.natAbs_ediv,Int.natAbs_natCast]
  have h : z.natAbs/denominator≤cap/denominator:=Nat.div_le_div_right small
  split <;> omega

#print axioms quotient_natAbs_le

/-- Concrete capacity for each actual real product in complex_multiply. The
bound is about the actual source-linked output, not an output assumption. -/
theorem rounded_product_magnitude_bound (a b out : Nat→Nat) (aStart bStart outStart : Nat)
    (aSmall : magnitude 1000000000 5 (fun k=>a (aStart+k))≤1000*unit)
    (bSmall : magnitude 1000000000 5 (fun k=>b (bStart+k))≤1000*unit)
    (correct : CanonicalSource.represented out outStart=
      (CanonicalSource.represented a aStart*CanonicalSource.represented b bStart)/(1000000000^4:Nat)) :
    magnitude 1000000000 5 (fun k=>out (outStart+k))≤1000000*unit+1:=by
  have productBound : (CanonicalSource.represented a aStart*CanonicalSource.represented b bStart).natAbs≤(1000*unit)*(1000*unit):=by
    simpa only [Int.natAbs_mul,represented_natAbs] using Nat.mul_le_mul aSmall bSmall
  have qbound : ((CanonicalSource.represented a aStart*CanonicalSource.represented b bStart)/(unit:Nat)).natAbs≤1000000*unit+1:=by
    have q:=quotient_natAbs_le _ unit _ productBound
    norm_num [unit] at q ⊢
    exact q
  have sameUnit : (1000000000^4:Nat)=unit:=by norm_num [unit]
  rw [sameUnit] at correct
  have equal:=congrArg Int.natAbs correct
  rw [represented_natAbs] at equal
  exact equal.trans_le qbound

#print axioms rounded_product_magnitude_bound

theorem sum_products_fits (a b : Nat) (ha : a≤1000000*unit+1) (hb : b≤1000000*unit+1) :
    a+b<1000000000^5:=by
  norm_num [unit] at ha hb ⊢
  omega

#print axioms sum_products_fits
end RH080Next.FFTPV.ComplexSource
