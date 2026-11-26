/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTForestTrace
import FFTRoundoff
import Mathlib.Data.List.GetD

set_option autoImplicit false
noncomputable section
namespace RH080Next.FFT.IntegerModel

/-- Read an unbounded signed integer pair in the source's 10^36 scale. -/
def decode (a : CInt) : ℂ := ⟨(a.1:ℝ)/(unit:ℝ),(a.2:ℝ)/(unit:ℝ)⟩

def roundedProduct (a b : ℝ) : ℝ := (⌊a*b*(unit:ℝ)⌋:ℤ)/(unit:ℝ)
def roundedComplex (a b : ℂ) : ℂ :=
  ⟨roundedProduct a.re b.re-roundedProduct a.im b.im,
    roundedProduct a.re b.im+roundedProduct a.im b.re⟩

theorem roundedProduct_error (a b : ℝ) :
    |roundedProduct a b-a*b|≤1/(unit:ℝ) := by
  have hp : 0<(unit:ℝ) := by norm_num [unit]
  have hl := Int.floor_le (a*b*(unit:ℝ))
  have hu := Int.lt_floor_add_one (a*b*(unit:ℝ))
  have hc := div_mul_cancel₀ (((⌊a*b*(unit:ℝ)⌋:ℤ):ℝ)) hp.ne'
  have hc1 := div_mul_cancel₀ (1:ℝ) hp.ne'
  unfold roundedProduct
  rw [abs_le]
  constructor <;> nlinarith

theorem roundedComplex_error (a b : ℂ) :
    ‖roundedComplex a b-a*b‖≤4/(unit:ℝ) := by
  simpa [roundedComplex,div_eq_mul_inv] using complex_four_product_rounding a b
    (roundedProduct a.re b.re) (roundedProduct a.im b.im)
    (roundedProduct a.re b.im) (roundedProduct a.im b.re) (1/(unit:ℝ))
    (roundedProduct_error _ _) (roundedProduct_error _ _)
    (roundedProduct_error _ _) (roundedProduct_error _ _)

theorem roundedComplex_comm (a b : ℂ) : roundedComplex a b=roundedComplex b a := by
  apply Complex.ext <;> simp [roundedComplex,roundedProduct,mul_comm,add_comm]

theorem decode_zero : decode (0,0)=0 := by apply Complex.ext <;> simp [decode]
theorem decode_unit : decode (unit,0)=1 := by apply Complex.ext <;> norm_num [decode,unit]
theorem decode_add (a b : CInt) : decode (add a b)=decode a+decode b := by
  apply Complex.ext <;> simp [decode,add,add_div]
theorem decode_sub (a b : CInt) : decode (sub a b)=decode a-decode b := by
  apply Complex.ext <;> simp [decode,sub,sub_div]

theorem roundedProduct_decode (a b : ℤ) :
    roundedProduct ((a:ℝ)/(unit:ℝ)) ((b:ℝ)/(unit:ℝ))=
      (((a*b)/unit:ℤ):ℝ)/(unit:ℝ) := by
  have h : (a:ℝ)/(unit:ℝ)*((b:ℝ)/(unit:ℝ))*(unit:ℝ)=((a*b:ℤ):ℝ)/(unit:ℝ) := by
    push_cast
    field_simp
  unfold roundedProduct
  rw [h,Int.floor_div_cast_of_nonneg (show 0≤unit by norm_num [unit]),Int.floor_intCast]

theorem decode_mul (a b : CInt) : decode (mul a b)=roundedComplex (decode a) (decode b) := by
  apply Complex.ext <;> simp only [decode,mul,roundedComplex,Complex.re,Complex.im,
    roundedProduct_decode,Int.cast_sub,Int.cast_add,sub_div,add_div]

/-- Pointwise arithmetic content of a trace, independent of its checker. -/
theorem MergeTrace.getD {as bs ws ps qs : List CInt} (h : MergeTrace as bs ws ps qs)
    (j : Nat) (hj : j<as.length) :
    ps.getD j (0,0)=add (as.getD j (0,0)) (mul (bs.getD j (0,0)) (ws.getD j (0,0))) ∧
    qs.getD j (0,0)=sub (as.getD j (0,0)) (mul (bs.getD j (0,0)) (ws.getD j (0,0))) := by
  induction h generalizing j with
  | nil => simp at hj
  | cons a b w p q as bs ws ps qs hp hq tail ih =>
    cases j with
    | zero => simpa using And.intro hp hq
    | succ j => simpa using ih j (by simpa using hj)

theorem ExecutionTrace.decode_roundedFFT {stages : Nat → List CInt} {input : Nat → CInt}
    {s index step : Nat} {out : List CInt} (h : ExecutionTrace stages input s index step out)
    (k : Nat) (hk : k<2^s) :
    decode (out.getD k (0,0))=
      roundedFFT (fun t j => decode ((stages t).getD j (0,0))) roundedComplex s
        (fun j => decode (input (index+step*j))) k := by
  induction h generalizing k with
  | leaf index step =>
    have hk0 : k=0 := by simpa using hk
    subst k
    simp [roundedFFT]
  | node s index step as bs ps qs left right merge ihl ihr =>
    have ha : as.length=2^s := left.output_length
    have hb : bs.length=2^s := right.output_length
    have hp : ps.length=2^s := by rw [←merge.lengths.2.2.1,ha]
    have hq : qs.length=2^s := by rw [←merge.lengths.2.2.2,ha]
    have hleft : (fun j => decode (input (index+(step*2)*j)))=
        (fun j => decode (input (index+step*(2*j)))) := by
      funext j
      congr 2
      ring
    have hright : (fun j => decode (input ((index+step)+(step*2)*j)))=
        (fun j => decode (input (index+step*(2*j+1)))) := by
      funext j
      congr 2
      ring
    by_cases hh : k<2^s
    · have hm := merge.getD k (by omega)
      rw [List.getD_append _ _ _ _ (by omega),hm.1,decode_add,decode_mul,
        roundedComplex_comm,ihl k hh,ihr k hh,hleft,hright]
      simp only [roundedFFT,hh,if_pos]
    · have hj : k-2^s<2^s := by rw [Nat.pow_succ] at hk; omega
      have hm := merge.getD (k-2^s) (by omega)
      rw [List.getD_append_right _ _ _ _ (by omega),hp,hm.2,decode_sub,decode_mul,
        roundedComplex_comm,ihl _ hj,ihr _ hj,hleft,hright]
      simp only [roundedFFT,hh,if_false]

/-- Decimation retains exact globally generated entries, including defaults. -/
theorem EvenTrace.getD {as bs : List CInt} (h : EvenTrace as bs) (j : Nat) :
    bs.getD j (0,0)=as.getD (2*j) (0,0) := by
  induction h generalizing j with
  | nil => simp
  | one a =>
    cases j with
    | zero => simp
    | succ j => simp
  | cons a b as evens tail ih =>
    cases j with
    | zero => simp
    | succ j => simpa [Nat.mul_add] using ih j

#print axioms roundedProduct_error
#print axioms roundedComplex_error
#print axioms decode_mul
#print axioms ExecutionTrace.decode_roundedFFT
#print axioms EvenTrace.getD
end RH080Next.FFT.IntegerModel
