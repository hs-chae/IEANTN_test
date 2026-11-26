/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTWordBounds
import WindowData
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace RH080Next.FFTPV.InputScaling
open WindowPV

def magnitude (e : Nat) : Nat := if Data.scale≤e then e-Data.scale else Data.scale-e

def initialDigits (value : Nat) : Nat :=
  (value*100%1000000000)*1000000000^2+
    ((value*100/1000000000)%1000000000)*1000000000^3+
    (value*100/1000000000/1000000000)*1000000000^4

theorem initialDigits_exact (value : Nat) : initialDigits value=value*100000000000000000000 := by
  unfold initialDigits
  norm_num
  omega

theorem magnitude_bound (e : Nat) (he : e<2*Data.scale) : magnitude e≤Data.scale := by
  unfold magnitude
  split <;> omega

theorem initial_word_safe (e : Nat) (he : e<2*Data.scale) : magnitude e*100<2^64 := by
  have h := magnitude_bound e he
  norm_num [Data.scale] at h ⊢
  omega

/-- Exactly the sign and fixed-point placement used by the actual C input
initialization, including negative coefficients. -/
theorem initial_real_value (e : Nat) :
    (if Data.scale≤e then (initialDigits (magnitude e) : ℚ)/1000000000000000000000000000000000000
      else -(initialDigits (magnitude e) : ℚ)/1000000000000000000000000000000000000) =
    (((e:Int)-(Data.scale:Int) : Int) : ℚ)/(Data.scale : ℚ) := by
  rw [initialDigits_exact]
  unfold magnitude
  by_cases h : Data.scale≤e
  · simp only [h,↓reduceIte]
    rw [Nat.cast_mul,Nat.cast_sub h]
    push_cast
    norm_num [Data.scale]
    ring
  · have h' : e≤Data.scale := by omega
    simp only [h,↓reduceIte]
    rw [Nat.cast_mul,Nat.cast_sub h']
    push_cast
    norm_num [Data.scale]
    ring

def inputMassNumerator : Nat := magnitude (Data.encoded.headD Data.scale)+
  2*((Data.encoded.drop 1).map magnitude).sum

theorem inputMass_exact : inputMassNumerator=3612586121968140058 := by decide +kernel

theorem inputMass_bound : (inputMassNumerator : ℚ)/10000000000000000<362 := by
  rw [inputMass_exact]
  norm_num

/-- The exact numerical consequence required by the source's +100-unit error
allowance, once the source FFT refinement has supplied these generic errors. -/
theorem roundoff_allowance :
    (((1+(1/10000000000000000000 : ℚ))^24-1)*362+
      (2^24-1)*(1+(1/10000000000000000000 : ℚ))^24*
        (4/1000000000000000000000000000000000000 : ℚ)) <
      100/10000000000000000 := by decide +kernel

#print axioms initialDigits_exact
#print axioms initial_real_value
#print axioms inputMass_exact
#print axioms roundoff_allowance
end RH080Next.FFTPV.InputScaling
