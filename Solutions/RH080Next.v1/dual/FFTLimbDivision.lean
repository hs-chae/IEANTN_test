/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTLimbAddition

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace RH080Next.FFT.Limbs

def prependDigit (v : ℕ) (d : ℕ → ℕ) (j : ℕ) : ℕ := if j=0 then v else d (j-1)

theorem magnitude_prepend (B n v : ℕ) (d : ℕ → ℕ) :
    magnitude B (n+1) (prependDigit v d)=v+B*magnitude B n d := by
  rw [show n+1=1+n by omega,magnitude_split]
  have he : (fun j => prependDigit v d (1+j))=d := by
    funext j
    simp [prependDigit,show 1+j≠0 by omega,show 1+j-1=j by omega]
  rw [he]
  simp [magnitude,prependDigit]

/-- Source divide_small, from the highest digit to the lowest. Its input
digits are mathematical original digits; the source proof must establish
that in-place stores preserve every lower, unread digit. -/
def divideDigits (B D : ℕ) (a : ℕ → ℕ) : ℕ → ((ℕ → ℕ) × ℕ)
  | 0 => (fun _ => 0,0)
  | n+1 =>
    let r := divideDigits B D (fun j => a (j+1)) n
    let t := r.2*B+a 0
    (prependDigit (t/D) r.1,t%D)

theorem divideDigits_value (B D n : ℕ) (a : ℕ → ℕ) :
    magnitude B n a=D*magnitude B n (divideDigits B D a n).1+(divideDigits B D a n).2 := by
  induction n generalizing a with
  | zero => simp [divideDigits,magnitude]
  | succ n ih =>
    let r := divideDigits B D (fun j => a (j+1)) n
    let t := r.2*B+a 0
    have hi := ih (fun j => a (j+1))
    change magnitude B n (fun j => a (j+1))=D*magnitude B n r.1+r.2 at hi
    have hmul := congrArg (fun v : ℕ => B*v) hi
    have hd : t%D+D*(t/D)=r.2*B+a 0 := Nat.mod_add_div t D
    change magnitude B (n+1) a=D*magnitude B (n+1) (prependDigit (t/D) r.1)+t%D
    rw [magnitude_prepend,show n+1=1+n by omega,magnitude_split]
    have hshift : (fun j => a (1+j))=(fun j => a (j+1)) := by funext j; rw [Nat.add_comm]
    rw [hshift]
    simp only [magnitude,Finset.sum_range_one,pow_zero,mul_one,pow_one] at hmul ⊢
    nlinarith only [hmul,hd]

theorem divideDigits_remainder_lt (B D n : ℕ) (hD : 0 < D) (a : ℕ → ℕ) :
    (divideDigits B D a n).2 < D := by
  cases n with
  | zero => exact hD
  | succ n => exact Nat.mod_lt _ hD

theorem divideDigits_quotient_remainder (B D n : ℕ) (hD : 0 < D) (a : ℕ → ℕ) :
    magnitude B n (divideDigits B D a n).1=magnitude B n a/D ∧
      (divideDigits B D a n).2=magnitude B n a%D := by
  have h := divideDigits_value B D n a
  have hr := divideDigits_remainder_lt B D n hD a
  constructor
  · rw [h,Nat.add_comm,Nat.add_mul_div_left _ _ hD,Nat.div_eq_of_lt hr,zero_add]
  · rw [h,Nat.add_mod]
    simp [Nat.mod_eq_of_lt hr]

theorem divideDigits_bounds (B D n : ℕ) (hB : 0 < B) (hD : 0 < D) (a : ℕ → ℕ)
    (ha : ∀ j < n, a j < B) : ∀ j < n, (divideDigits B D a n).1 j < B := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    have ha' : ∀ j < n, a (j+1) < B := fun j hj => ha (j+1) (by omega)
    have hi := ih (fun j => a (j+1)) ha'
    have hr := divideDigits_remainder_lt B D n hD (fun j => a (j+1))
    have hm := Nat.mul_le_mul_right B (show (divideDigits B D (fun j => a (j+1)) n).2+1 ≤ D by omega)
    have ht : (divideDigits B D (fun j => a (j+1)) n).2*B+a 0 < B*D := by
      nlinarith [ha 0 (by omega)]
    intro j hj
    by_cases he : j=0
    · subst j
      simp only [divideDigits,prependDigit,↓reduceIte]
      exact (Nat.div_lt_iff_lt_mul hD).mpr ht
    · simp only [divideDigits,prependDigit,he,↓reduceIte]
      exact hi (j-1) (by omega)

def ceilQuotient (P D : ℕ) : ℕ := P/D+(if P%D=0 then 0 else 1)

/-- Exact ceiling operation used after divide_small when ceiling is set.
The source's increment_words contract must supply this final increment. -/
theorem ceilQuotient_bounds (P D : ℕ) (hD : 0 < D) :
    P ≤ D*ceilQuotient P D ∧ D*ceilQuotient P D < P+D := by
  have hd := Nat.mod_add_div P D
  have hr := Nat.mod_lt P hD
  unfold ceilQuotient
  by_cases hz : P%D=0
  · simp only [hz,↓reduceIte,add_zero] at *
    constructor <;> nlinarith
  · simp only [hz,↓reduceIte]
    have hp := Nat.pos_of_ne_zero hz
    constructor <;> nlinarith

#print axioms divideDigits_value
#print axioms divideDigits_quotient_remainder
#print axioms divideDigits_bounds
#print axioms ceilQuotient_bounds
end RH080Next.FFT.Limbs
