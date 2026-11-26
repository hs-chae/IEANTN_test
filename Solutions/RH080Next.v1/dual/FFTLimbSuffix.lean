/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTLimbAddition
import FFTLimbIncrement

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace RH080Next.FFT.Limbs

/-- The actual zero-status suffix, with its carry kept until it is proved zero.
The source refinement must establish the retained-output equation and status;
this lemma does not assume the desired quotient or a trusted output oracle. -/
theorem successful_product_suffix (B : ℕ) (hB : 0 < B) (d : ℕ → ℕ)
    (hd : ∀ j < 10, d j < B) (negative : Bool) (output carry : ℕ)
    (houtput : output+carry*B^5=magnitude B 5 (fun j => d (j+4))+
      (if negative && decide ((∑ j ∈ Finset.range 4, d j)≠0) then 1 else 0))
    (hstatus : d 9+carry=0) :
    signed negative output=
      (if negative then -(magnitude B 10 d:ℤ) else (magnitude B 10 d:ℤ))/(B^4:ℕ) := by
  obtain ⟨h9,hc⟩ := Nat.add_eq_zero.mp hstatus
  simp only [hc,Nat.zero_mul,Nat.add_zero] at houtput
  have hf := normalizedProduct_eq_floor B hB d hd h9 negative
  rw [←hf]
  cases negative with
  | false => simp only [Bool.false_and,Bool.false_eq_true,ite_false,Nat.add_zero] at houtput
             simp only [signed,normalizedProduct,Bool.false_eq_true,ite_false,houtput]
  | true =>
    by_cases hz : (∑ j ∈ Finset.range 4, d j)=0
    · simp [hz] at houtput
      simp [signed,normalizedProduct,hz,houtput]
    · simp [hz] at houtput
      simp [signed,normalizedProduct,hz,houtput]
      ring

#print axioms successful_product_suffix
end RH080Next.FFT.Limbs
