/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTSeedBounds

set_option autoImplicit false
noncomputable section
open Real
namespace RH080Next.FFT

/-- Error accumulated by the actual repeated-multiplication algorithm, once
its source refinement establishes the stated initial value and local errors.
There is no unverified source execution assumption hidden in the definition. -/
theorem repeated_twiddle_error (z : ℕ → ℂ) (seed exact : ℂ)
    (K : ℕ) (epsilon delta : ℝ) (he : 0≤epsilon) (hd : 0≤delta)
    (hseed : ‖seed-exact‖≤epsilon) (hunit : ‖exact‖=1) (hz : z 0=1)
    (hstep : ∀ j<K, ‖z (j+1)-seed*z j‖≤delta) :
    ∀ k≤K, ‖z k-exact^k‖≤(k:ℝ)*(epsilon+delta)*(1+epsilon)^k := by
  intro k hk
  induction k with
  | zero => simp [hz]
  | succ k ih =>
    have hkK : k<K := by omega
    have hi := ih (by omega)
    have hepow : 1≤(1+epsilon)^k := one_le_pow₀ (by linarith)
    have h := twiddle_step_error seed exact (z k) (exact^k) (z (k+1))
      ((k:ℝ)*(epsilon+delta)*(1+epsilon)^k) epsilon delta hi hseed hunit
      (by rw [norm_pow,hunit,one_pow]) he (hstep k hkK)
    have hlast : epsilon+delta≤(epsilon+delta)*(1+epsilon)^(k+1) :=
      le_mul_of_one_le_right (add_nonneg he hd) (one_le_pow₀ (by linarith))
    rw [pow_succ,Nat.cast_add,Nat.cast_one]
    rw [mul_comm (exact^k) exact]
    calc
      ‖z (k+1)-exact*exact^k‖ ≤
          (1+epsilon)*((k:ℝ)*(epsilon+delta)*(1+epsilon)^k)+epsilon+delta := h
      _ ≤ ((k:ℝ)+1)*(epsilon+delta)*((1+epsilon)^k*(1+epsilon)) := by
        rw [pow_succ] at hlast
        nlinarith

theorem small_growth_bound (epsilon : ℝ) (he : 0≤epsilon) (k : ℕ)
    (hk : (k:ℝ)*epsilon≤1/100) : (1+epsilon)^k≤(11/10:ℝ) := by
  calc
    _ ≤ (exp epsilon)^k := pow_le_pow_left₀ (by linarith)
      (by simpa [add_comm] using add_one_le_exp epsilon) k
    _ = exp ((k:ℝ)*epsilon) := (exp_nat_mul epsilon k).symm
    _ ≤ exp (1/100) := exp_le_exp.mpr hk
    _ ≤ (1:ℝ)/(1-1/100) := exp_bound_div_one_sub_of_interval (by norm_num) (by norm_num)
    _ ≤ _ := by norm_num

/-- Uniform twiddle budget for every entry actually read by a 2^24 FFT.
The abstract recurrence hypotheses are the source verification obligations;
all root approximation and long-recurrence arithmetic below are kernel-proved. -/
theorem fft24_twiddle_bound (z : ℕ → ℂ) (hz : z 0=1)
    (hstep : ∀ j<8388608, ‖z (j+1)-rootSeed*z j‖≤
      (4/1000000000000000000000000000000000000:ℝ))
    (k : ℕ) (hk : k≤8388608) :
    ‖z k-negativeRoot 16777216^k‖≤(1/10000000000000000000:ℝ) := by
  have h := repeated_twiddle_error z rootSeed (negativeRoot 16777216) 8388608
    (1/100000000000000000000000000:ℝ)
    (4/1000000000000000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) rootSeed_error (negativeRoot_norm _) hz hstep k hk
  have hkr : (k:ℝ)≤8388608 := by exact_mod_cast hk
  have hg := small_growth_bound (1/100000000000000000000000000:ℝ) (by norm_num) k
    (by linarith : (k:ℝ)*(1/100000000000000000000000000:ℝ)≤1/100)
  have hm := mul_le_mul_of_nonneg_left hg
    (show 0≤(k:ℝ)*((1/100000000000000000000000000:ℝ)+
      4/1000000000000000000000000000000000000) by positivity)
  exact h.trans (by nlinarith)

#print axioms repeated_twiddle_error
#print axioms small_growth_bound
#print axioms fft24_twiddle_bound
end RH080Next.FFT
