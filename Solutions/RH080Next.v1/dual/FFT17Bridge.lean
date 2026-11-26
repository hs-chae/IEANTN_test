/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTRoundoff
import FFT17SeedBounds

set_option autoImplicit false
noncomputable section
namespace RH080Next.FFT

/-- The mathematical reading of the C program's global twiddle table. At
stage s the source divides the full length by 2^s, the equality proved below. -/
def globalTwiddle17 (z : ℕ → ℂ) (s j : ℕ) : ℂ := z (j*2^(17-s))

theorem fft17_stage_stride (s : ℕ) (hs : s≤17) :
    131072/2^s=2^(17-s) := by
  have hp : (2:ℕ)^s*2^(17-s)=131072 := by
    rw [←pow_add,Nat.add_sub_of_le hs]
    norm_num
  exact Nat.div_eq_of_eq_mul_left (by positivity) (by simpa only [Nat.mul_comm] using hp.symm)

theorem globalTwiddle17_bound (z : ℕ → ℂ) (hz : z 0=1)
    (hstep : ∀ j<65536, ‖z (j+1)-rootSeed17*z j‖≤
      (4/1000000000000000000000000000000000000:ℝ)) :
    ∀ t<17, ∀ j<2^t,
      ‖globalTwiddle17 z (t+1) j-negativeRoot (2*2^t)^j‖≤
        (1/100000000000000000000:ℝ) := by
  intro t ht j hj
  have hts : t+1≤17 := by omega
  have hpow : (2*2^t)*2^(17-(t+1))=131072 := by
    rw [show 2*2^t=(2:ℕ)^(t+1) by rw [pow_succ,Nat.mul_comm],←pow_add,
      Nat.add_sub_of_le hts]
    norm_num
  have hjbound : j*2^(17-(t+1))≤65536 := by
    have h := Nat.mul_lt_mul_of_pos_right hj (show 0<(2:ℕ)^(17-(t+1)) by positivity)
    have he : (2:ℕ)^t*2^(17-(t+1))=65536 := by nlinarith [hpow]
    rw [he] at h
    omega
  have hr : negativeRoot 131072^2^(17-(t+1))=negativeRoot (2*2^t) := by
    rw [←hpow]
    exact negativeRoot_product_power _ _ (by positivity)
  have hex : negativeRoot 131072^(j*2^(17-(t+1)))=
      negativeRoot (2*2^t)^j := by
    rw [Nat.mul_comm j, pow_mul, hr]
  have h := fft17_twiddle_bound z hz hstep (j*2^(17-(t+1))) hjbound
  simpa only [globalTwiddle17,hex] using h

/-- Full mathematical fixed-point FFT error for the locked Fap input mass.
This is not a source-execution theorem: the concrete C proof still must
establish the table recurrence and its local multiplier/refinement facts. -/
theorem fft17_dft_error (z : ℕ → ℂ) (hz : z 0=1)
    (hstep : ∀ j<65536, ‖z (j+1)-rootSeed17*z j‖≤
      (4/1000000000000000000000000000000000000:ℝ))
    (mul : ℂ → ℂ → ℂ)
    (hmul : ∀ a b : ℂ, ‖mul a b-a*b‖≤
      (4/1000000000000000000000000000000000000:ℝ))
    (f : ℕ → ℂ) (hMass : coefficientMass (2^17) f≤81)
    (k : ℕ) (hk : k<2^17) :
    ‖roundedFFT (globalTwiddle17 z) mul 17 f k-
      dftSum (2^17) k (negativeRoot (2^17)) f‖≤(1/50000000000000000:ℝ) := by
  have h := roundedFFT_dft_error 17 f k hk (globalTwiddle17 z) mul
    (1/100000000000000000000:ℝ)
    (4/1000000000000000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (globalTwiddle17_bound z hz hstep) hmul
  have hp : 0≤(1+(1/100000000000000000000:ℝ))^17-1 := by
    have := one_le_pow₀ (n := 17) (by norm_num : (1:ℝ)≤1+1/100000000000000000000)
    linarith
  have hm := mul_le_mul_of_nonneg_left hMass hp
  have hb :
      ((1+(1/100000000000000000000:ℝ))^17-1)*81+
        ((2:ℝ)^17-1)*(1+(1/100000000000000000000:ℝ))^17*
          (4/1000000000000000000000000000000000000:ℝ)≤1/50000000000000000 := by
    norm_num
  exact h.trans (by linarith)

#print axioms fft17_stage_stride
#print axioms globalTwiddle17_bound
#print axioms fft17_dft_error
end RH080Next.FFT
