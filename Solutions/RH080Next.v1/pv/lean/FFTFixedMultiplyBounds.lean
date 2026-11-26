/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTFixedMultiplyBeginSource
set_option autoImplicit false
set_option maxHeartbeats 0
open scoped BigOperators
namespace RH080Next.FFTPV.MultiplyBounds
open GoldbachDirect GoldbachDirect.Semantics WordArrays

/-- The top scratch digit is zero whenever the exact full product is below
the weight of that digit; no certificate or observed overflow is assumed. -/
theorem top_digit_zero (d : Nat→Nat)
    (small : RH080Next.FFT.Limbs.magnitude 1000000000 10 d<1000000000^9) : d 9=0 := by
  have digitLe : d 9*1000000000^9≤RH080Next.FFT.Limbs.magnitude 1000000000 10 d:=by
    unfold RH080Next.FFT.Limbs.magnitude
    exact Finset.single_le_sum (fun j _=>Nat.zero_le (d j*1000000000^j)) (Finset.mem_range.mpr (by decide : 9<10))
  by_contra nonzero
  have atLeastOne : 1≤d 9:=by omega
  have powerLe:=Nat.mul_le_mul_right (1000000000^9) atLeastOne
  exact (not_lt_of_ge (by simpa using powerLe.trans digitLe)) small

/-- A reusable safe-call bound for source fixed_multiply. The actual FFT
consumer must establish its input magnitude bounds, not infer them from output.
1000 in decoded scale 10^36 leaves substantial room below source word overflow. -/
theorem bounded_product (a b d : Nat→Nat)
    (product : RH080Next.FFT.Limbs.value 1000000000 10 d=
      RH080Next.FFT.Limbs.value 1000000000 5 a*RH080Next.FFT.Limbs.value 1000000000 5 b)
    (aBound : RH080Next.FFT.Limbs.magnitude 1000000000 5 a≤1000*10^36)
    (bBound : RH080Next.FFT.Limbs.magnitude 1000000000 5 b≤1000*10^36)
    (digits : ∀k,k<10 → d k<1000000000) :
    d 9=0 ∧ RH080Next.FFT.Limbs.magnitude 1000000000 5 (fun j=>d (j+4))+1<1000000000^5 := by
  have naturalProduct : RH080Next.FFT.Limbs.magnitude 1000000000 10 d=
      RH080Next.FFT.Limbs.magnitude 1000000000 5 a*RH080Next.FFT.Limbs.magnitude 1000000000 5 b:=by
    simpa only [RH080Next.FFT.Limbs.value_eq_magnitude,←Nat.cast_mul,Int.natCast_inj] using product
  have bound : RH080Next.FFT.Limbs.magnitude 1000000000 10 d≤(1000*10^36)*(1000*10^36):=by
    rw [naturalProduct];exact Nat.mul_le_mul aBound bBound
  have small : RH080Next.FFT.Limbs.magnitude 1000000000 10 d<1000000000^9:=
    bound.trans_lt (by norm_num)
  have top:=top_digit_zero d small
  have drop:=RH080Next.FFT.Limbs.drop_four_digits 1000000000 (by norm_num) d digits top
  have division : RH080Next.FFT.Limbs.magnitude 1000000000 10 d/1000000000^4≤
      ((1000*10^36)*(1000*10^36))/1000000000^4:=Nat.div_le_div_right bound
  refine ⟨top,?_⟩
  rw [←drop.1]
  exact (Nat.add_le_add_right division 1).trans_lt (by norm_num)

/-- Every real source product-core execution under bounded represented inputs
has zero overflow word and room for the negative-product increment. -/
theorem source_core_safe {F : Type} {context : Context F} {before after : State F} {flow : Flow}
    {aObj aSize aStart bObj bSize bStart workObj workSize workStart : Nat}
    {ids owners : ProductOuter.PVar→Nat} {a b data : Nat→Nat}
    (h : ProductOuter.View before aObj aSize aStart bObj bSize bStart workObj workSize workStart ids owners a b data 0)
    (initialized : ∀k,k<10 → data (workStart+k)=0)
    (aBound : RH080Next.FFT.Limbs.magnitude 1000000000 5 a≤1000*10^36)
    (bBound : RH080Next.FFT.Limbs.magnitude 1000000000 5 b≤1000*10^36)
    (run : Exec context before ProductOuter.outerLoop flow after) :
    flow=.normal ∧ ∃finalData,
      ProductOuter.View after aObj aSize aStart bObj bSize bStart workObj workSize workStart ids owners a b finalData 5 ∧
      finalData (workStart+9)=0 ∧
      RH080Next.FFT.Limbs.magnitude 1000000000 5 (fun j=>finalData (workStart+(j+4)))+1<1000000000^5 := by
  obtain ⟨normal,finalData,ha,frame,product⟩:=ProductOuter.every_source_product_core h initialized run
  obtain ⟨top,room⟩:=bounded_product a b (fun k=>finalData (workStart+k)) product aBound bBound ha.workDigits
  exact ⟨normal,finalData,ha,top,room⟩

#print axioms top_digit_zero
#print axioms bounded_product
#print axioms source_core_safe
end RH080Next.FFTPV.MultiplyBounds
