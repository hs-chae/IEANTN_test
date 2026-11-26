/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFT24Bridge

set_option autoImplicit false
noncomputable section
open Real
open scoped BigOperators
namespace RH080Next.FFT

def deltaInput (j : ℕ) (a : ℂ) (l : ℕ) : ℂ := if l=j then a else 0

def mirroredInput (N n : ℕ) (a : ℕ → ℝ) (l : ℕ) : ℂ :=
  deltaInput 0 (a 0) l+
    ∑ j ∈ Finset.Ico 1 n, (deltaInput j (a j) l+deltaInput (N-j) (a j) l)

theorem dft_deltaInput (N k j : ℕ) (ω a : ℂ) (hj : j<N) :
    dftSum N k ω (deltaInput j a)=a*ω^(j*k) := by
  simp [dftSum,deltaInput,ite_mul,Finset.mem_range.mpr hj]

theorem dft_add (N k : ℕ) (ω : ℂ) (f g : ℕ → ℂ) :
    dftSum N k ω (fun j => f j+g j)=dftSum N k ω f+dftSum N k ω g := by
  simp [dftSum,add_mul,Finset.sum_add_distrib]

theorem dft_finite_sum (N k : ℕ) (ω : ℂ) (s : Finset ℕ) (f : ℕ → ℕ → ℂ) :
    dftSum N k ω (fun l => ∑ j ∈ s, f j l)=∑ j ∈ s, dftSum N k ω (f j) := by
  simp only [dftSum,Finset.sum_mul]
  exact Finset.sum_comm

theorem mirrored_dft (N n k : ℕ) (a : ℕ → ℝ) (ω : ℂ)
    (hN : 0<N) (hn : n≤N) :
    dftSum N k ω (mirroredInput N n a)=
      (a 0:ℂ)+∑ j ∈ Finset.Ico 1 n,
        ((a j:ℂ)*ω^(j*k)+(a j:ℂ)*ω^((N-j)*k)) := by
  unfold mirroredInput
  rw [dft_add,dft_deltaInput N k 0 ω _ hN,dft_finite_sum]
  simp only [Nat.zero_mul,pow_zero,mul_one]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hj1 := (Finset.mem_Ico.mp hj).1
  have hjn := (Finset.mem_Ico.mp hj).2
  rw [dft_add,dft_deltaInput N k j ω _ (by omega),
    dft_deltaInput N k (N-j) ω _ (by omega)]

theorem negativeRoot_power_re (N r : ℕ) :
    (negativeRoot N^r).re=cos (2*π*(r:ℝ)/(N:ℝ)) := by
  unfold negativeRoot
  rw [←Complex.exp_nat_mul,Complex.exp_re]
  have he : (r:ℂ)*(-2*(π:ℂ)*Complex.I/(N:ℂ)) =
      (((-(2*π*(r:ℝ)/(N:ℝ))):ℝ):ℂ)*Complex.I := by
    push_cast
    ring
  rw [he]
  simp [Complex.mul_re,Complex.mul_im]

/-- Exact transform identity for the even mirrored coefficient input actually
used by both C FFT programs. It establishes the real nodal cosine samples,
not a generic transform with an unproved cosine-kernel identification. -/
theorem mirrored_dft_re (N n k : ℕ) (a : ℕ → ℝ)
    (hN : 0<N) (hn : n≤N) :
    (dftSum N k (negativeRoot N) (mirroredInput N n a)).re=
      a 0+2*∑ j ∈ Finset.Ico 1 n,
        a j*cos (2*π*(j:ℝ)*((k:ℝ)/(N:ℝ))) := by
  have sum_re (s : Finset ℕ) (f : ℕ → ℂ) :
      (∑ j ∈ s, f j).re=∑ j ∈ s, (f j).re := map_sum Complex.reCLM f s
  rw [mirrored_dft N n k a _ hN hn]
  simp only [sum_re,Complex.add_re,Complex.ofReal_re,Complex.mul_re,
    Complex.ofReal_im,zero_mul,sub_zero,negativeRoot_power_re]
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hjN : j≤N := le_trans (Finset.mem_Ico.mp hj).2.le hn
  have hNr : (N:ℝ)≠0 := by exact_mod_cast hN.ne'
  rw [Nat.cast_mul,Nat.cast_mul,Nat.cast_sub hjN]
  have he : 2*π*((N:ℝ)-(j:ℝ))*(k:ℝ)/(N:ℝ)=
      (k:ℝ)*(2*π)-2*π*(j:ℝ)*((k:ℝ)/(N:ℝ)) := by field_simp <;> ring
  have he' : 2*π*((j:ℝ)*(k:ℝ))/(N:ℝ)=2*π*(j:ℝ)*((k:ℝ)/(N:ℝ)) := by ring
  rw [he',show 2*π*(((N:ℝ)-(j:ℝ))*(k:ℝ))/(N:ℝ)=
      (k:ℝ)*(2*π)-2*π*(j:ℝ)*((k:ℝ)/(N:ℝ)) by convert he using 1 <;> ring,
    cos_nat_mul_two_pi_sub]
  ring

#print axioms mirrored_dft
#print axioms negativeRoot_power_re
#print axioms mirrored_dft_re
end RH080Next.FFT
