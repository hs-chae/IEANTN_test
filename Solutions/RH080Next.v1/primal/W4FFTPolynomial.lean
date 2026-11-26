/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import W4FFTInput
import ExplicitAffineWindow
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
noncomputable section
open scoped BigOperators
namespace RH080Next.Primal.W4FFTKernel
open RH080Next.FFT RH080Next.FFT.IntegerModel

private theorem dirac_dft (n k r : Nat) (ω a : ℂ) :
    (∑j ∈ Finset.range n, (if j=r then a else 0)*ω^(j*k)) =
      if r<n then a*ω^(r*k) else 0 := by
  by_cases hr : r<n
  · rw [if_pos hr, Finset.sum_eq_single r]
    · simp
    · intro j hj hne; simp [hne]
    · intro absent; exact False.elim (absent (Finset.mem_range.mpr hr))
  · rw [if_neg hr]
    apply Finset.sum_eq_zero
    intro j hj
    have hne : j≠r := by intro he; subst j; exact hr (Finset.mem_range.mp hj)
    simp [hne]

/-- The exact DFT of the sparse symmetric coefficient array. -/
theorem dft_symmetric (n d k : Nat) (hd : d≤n) (ω : ℂ) (a : Nat → ℂ) :
    dftSum n k ω (symmetricInput n d a) =
      ∑j ∈ Finset.range d, (a j*ω^(j*k) + if j=0 then 0 else a j*ω^((n-j)*k)) := by
  unfold dftSum symmetricInput
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib, dirac_dft, dirac_dft,
    if_pos (show j<n by have h := Finset.mem_range.mp hj; omega)]
  by_cases hz : j=0
  · subst j; simp
  · rw [if_neg hz, if_pos (show n-j<n by have h := Finset.mem_range.mp hj; omega)]

/-- The true real part of each negative complex Fourier root power. -/
theorem negativeRoot_pow_re (n r : Nat) (hn : 0<n) :
    (negativeRoot n^r).re = Real.cos (2*Real.pi*(r:ℝ)/(n:ℝ)) := by
  have hnc : (n:ℂ)≠0 := by exact_mod_cast hn.ne'
  unfold negativeRoot
  rw [← Complex.exp_nat_mul]
  have he : (r:ℂ)*(-2*(Real.pi:ℂ)*Complex.I/(n:ℂ)) =
      ((-(2*Real.pi*(r:ℝ)/(n:ℝ)):ℝ):ℂ)*Complex.I := by
    push_cast
    field_simp
    <;> ring
  rw [he]
  simp [Complex.exp_re, Real.cos_neg]

private theorem mirror_cos (n j k : Nat) (hn : 0<n) (hj : j≤n) :
    Real.cos (2*Real.pi*((n-j)*k:Nat)/(n:ℝ)) =
      Real.cos (2*Real.pi*(j*k:Nat)/(n:ℝ)) := by
  have hnr : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  have he : (2*Real.pi*((n-j)*k:Nat)/(n:ℝ)) =
      (k:ℝ)*(2*Real.pi)-2*Real.pi*(j*k:Nat)/(n:ℝ) := by
    rw [Nat.cast_mul, Nat.cast_sub hj, Nat.cast_mul]
    field_simp
    <;> ring
  rw [he, Real.cos_nat_mul_two_pi_sub]

def seriesWeight (a : Nat → ℝ) (j : Nat) : ℝ := (if j=0 then 1 else 2)*a j
def frequency (j : Nat) : ℝ := 2*Real.pi*j

def cosineSeries (d : Nat) (a : Nat → ℝ) (y : ℝ) : ℝ :=
  ∑j ∈ Finset.range d, seriesWeight a j*Real.cos (frequency j*y)

/-- The real DFT samples are the actual real cosine polynomial samples. -/
theorem dft_symmetric_re (n d k : Nat) (hn : 0<n) (hd : d≤n) (a : Nat → ℝ) :
    (dftSum n k (negativeRoot n) (symmetricInput n d (fun j => (a j:ℂ)))).re =
      cosineSeries d a ((k:ℝ)/n) := by
  rw [dft_symmetric n d k hd, Complex.re_sum]
  unfold cosineSeries
  apply Finset.sum_congr rfl
  intro j hj
  rw [Complex.add_re]
  have hp : ((a j:ℂ)*negativeRoot n^(j*k)).re =
      a j*Real.cos (2*Real.pi*(j*k:Nat)/(n:ℝ)) := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      negativeRoot_pow_re n (j*k) hn]
  rw [hp]
  by_cases hz : j=0
  · subst j
    simp [seriesWeight, frequency]
  · rw [if_neg hz]
    have hq : ((a j:ℂ)*negativeRoot n^((n-j)*k)).re =
        a j*Real.cos (2*Real.pi*(j*k:Nat)/(n:ℝ)) := by
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
        negativeRoot_pow_re n ((n-j)*k) hn]
      rw [mirror_cos n j k hn (by have h := Finset.mem_range.mp hj; omega)]
    rw [hq]
    simp only [seriesWeight, if_neg hz, frequency, Nat.cast_mul]
    have he : 2*Real.pi*((j:ℝ)*(k:ℝ))/(n:ℝ) = 2*Real.pi*(j:ℝ)*((k:ℝ)/(n:ℝ)) := by ring
    rw [he]
    ring

/-- Actual original integer W4.input, with its exact 10^16 coefficient scale. -/
theorem actual_dft_re (n k : Nat) (hn : 5040≤n) :
    (dftSum n k (negativeRoot n) (fun j => decode (W4.input n j))).re =
      cosineSeries 2520 realCoefficient ((k:ℝ)/n) := by
  have he : dftSum n k (negativeRoot n) (fun j => decode (W4.input n j)) =
      dftSum n k (negativeRoot n) (symmetricInput n 2520 (fun j => (realCoefficient j:ℂ))) := by
    unfold dftSum
    apply Finset.sum_congr rfl
    intro j hj
    dsimp only
    rw [decode_input_eq_symmetric n hn j (Finset.mem_range.mp hj)]
  rw [he]
  exact dft_symmetric_re n 2520 k (by omega) (by omega) realCoefficient

#print axioms negativeRoot_pow_re
#print axioms actual_dft_re
end RH080Next.Primal.W4FFTKernel
