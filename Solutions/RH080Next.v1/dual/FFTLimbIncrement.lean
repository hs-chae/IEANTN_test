/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTLimbAddition

set_option autoImplicit false
noncomputable section
namespace RH080Next.FFT.Limbs

/-- Exact carry-one recurrence of increment_words, before source refinement. -/
def incrementDigits (B : ℕ) (a : ℕ → ℕ) : ℕ → ((ℕ → ℕ) × ℕ)
  | 0 => (fun _ => 0,1)
  | n+1 =>
    let r := incrementDigits B a n
    let t := a n+r.2
    (Function.update r.1 n (t%B),t/B)

theorem incrementDigits_value (B n : ℕ) (a : ℕ → ℕ) :
    magnitude B n (incrementDigits B a n).1+(incrementDigits B a n).2*B^n=
      magnitude B n a+1 := by
  induction n with
  | zero => simp [incrementDigits,magnitude]
  | succ n ih =>
    let r := incrementDigits B a n
    let t := a n+r.2
    have hd : t%B+B*(t/B)=a n+r.2 := Nat.mod_add_div t B
    change magnitude B (n+1) (Function.update r.1 n (t%B))+(t/B)*B^(n+1)=_
    rw [magnitude_prefix_update,magnitude_succ,pow_succ]
    change magnitude B n r.1+r.2*B^n=_ at ih
    have hh := congrArg (fun z : ℕ => z*B^n) hd
    nlinarith only [ih,hh]

theorem incrementDigits_bounds (B n : ℕ) (hB : 2≤B) (a : ℕ → ℕ)
    (ha : ∀ j<n,a j<B) :
    (incrementDigits B a n).2≤1 ∧ ∀ j<n,(incrementDigits B a n).1 j<B := by
  induction n with
  | zero => simp [incrementDigits]
  | succ n ih =>
    obtain ⟨hc,hd⟩ := ih (fun j hj => ha j (by omega))
    constructor
    · change (a n+(incrementDigits B a n).2)/B≤1
      have han := ha n (by omega)
      have hlt : (a n+(incrementDigits B a n).2)/B<2 :=
        (Nat.div_lt_iff_lt_mul (show 0<B by omega)).mpr (by omega)
      omega
    · intro j hj
      change Function.update (incrementDigits B a n).1 n ((a n+(incrementDigits B a n).2)%B) j<B
      by_cases h : j=n
      · subst j
        simpa using Nat.mod_lt (a n+(incrementDigits B a n).2) (show 0<B by omega)
      · rw [Function.update_of_ne h]
        exact hd j (by omega)

theorem incrementDigits_no_overflow (B n : ℕ) (hB : 0<B) (a : ℕ → ℕ)
    (hsmall : magnitude B n a+1<B^n) :
    (incrementDigits B a n).2=0 ∧
      magnitude B n (incrementDigits B a n).1=magnitude B n a+1 := by
  have h := incrementDigits_value B n a
  have hc : (incrementDigits B a n).2=0 := by
    by_contra hh
    have hm := Nat.mul_le_mul_right (B^n) (Nat.one_le_iff_ne_zero.mpr hh)
    nlinarith
  exact ⟨hc,by simpa [hc] using h⟩

#print axioms incrementDigits_value
#print axioms incrementDigits_bounds
#print axioms incrementDigits_no_overflow
end RH080Next.FFT.Limbs
