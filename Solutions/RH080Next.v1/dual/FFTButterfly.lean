/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace RH080Next.FFT

def dftSum (n k : ℕ) (ω : ℂ) (f : ℕ → ℂ) : ℂ :=
  ∑ j ∈ Finset.range n, f j * ω ^ (j*k)

lemma sum_range_double (f : ℕ → ℂ) (n : ℕ) :
    (∑ j ∈ Finset.range (2*n), f j) = ∑ j ∈ Finset.range n, (f (2*j)+f (2*j+1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2*(n+1)=2*n+1+1 by omega, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, Finset.sum_range_succ]
    ring

/-- Exact even/odd factorization, without a root or numerical assumption. -/
theorem dft_even_odd (n k : ℕ) (ω : ℂ) (f : ℕ → ℂ) :
    dftSum (2*n) k ω f =
      dftSum n k (ω^2) (fun j => f (2*j)) +
      ω^k*dftSum n k (ω^2) (fun j => f (2*j+1)) := by
  have he (j : ℕ) : ω^((2*j)*k)=(ω^2)^(j*k) := by
    rw [← pow_mul]
    congr 1
    ring
  unfold dftSum
  rw [sum_range_double]
  simp_rw [Nat.add_mul, pow_add, he]
  rw [Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  simp only [one_mul]
  ring

lemma dft_frequency_period (n k : ℕ) (ω : ℂ) (f : ℕ → ℂ) (hω : ω^n=1) :
    dftSum n (k+n) ω f = dftSum n k ω f := by
  unfold dftSum
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : ω^(j*n)=1 := by rw [Nat.mul_comm, pow_mul, hω, one_pow]
  rw [Nat.mul_add, pow_add, hjn, mul_one]

/-- The second half of a radix-two butterfly is subtraction. This covers either
Fourier sign convention when the corresponding twiddle has ω^n=-1. -/
theorem dft_even_odd_second (n k : ℕ) (ω : ℂ) (f : ℕ → ℂ) (hω : ω^n=-1) :
    dftSum (2*n) (k+n) ω f =
      dftSum n k (ω^2) (fun j => f (2*j)) -
      ω^k*dftSum n k (ω^2) (fun j => f (2*j+1)) := by
  have hsq : (ω^2)^n=1 := by
    calc
      _ = (ω^n)^2 := by simp only [← pow_mul]; congr 1; ring
      _ = 1 := by rw [hω]; norm_num
  rw [dft_even_odd, dft_frequency_period n k (ω^2) _ hsq,
    dft_frequency_period n k (ω^2) _ hsq, pow_add, hω]
  ring

/-- Every exact transform row is bounded by the input coefficient L1 mass. -/
theorem norm_dft_le_mass (n k : ℕ) (ω : ℂ) (f : ℕ → ℂ) (hω : ‖ω‖=1) :
    ‖dftSum n k ω f‖ ≤ ∑ j ∈ Finset.range n, ‖f j‖ := by
  unfold dftSum
  calc
    _ ≤ ∑ j ∈ Finset.range n, ‖f j*ω^(j*k)‖ := norm_sum_le _ _
    _ = _ := by simp only [norm_mul, norm_pow, hω, one_pow, mul_one]

/-- Local butterfly error for an actual rounded multiplication result r.
The source-level refinement must establish hr and the input/twiddle bounds. -/
theorem butterfly_error
    (a b aa bb w ww r : ℂ) (ea eb eta delta B : ℝ)
    (ha : ‖aa-a‖≤ea) (hb : ‖bb-b‖≤eb)
    (hw : ‖w‖=1) (hww : ‖ww-w‖≤eta) (hB : ‖bb‖≤B)
    (heta : 0≤eta) (hr : ‖r-ww*bb‖≤delta) :
    ‖(aa+r)-(a+w*b)‖ ≤ ea+eb+eta*B+delta ∧
    ‖(aa-r)-(a-w*b)‖ ≤ ea+eb+eta*B+delta := by
  have hprod : ‖ww*bb-w*b‖ ≤ eta*B+eb := by
    calc
      _ = ‖(ww-w)*bb+w*(bb-b)‖ := by congr 1; ring
      _ ≤ ‖(ww-w)*bb‖+‖w*(bb-b)‖ := norm_add_le _ _
      _ = ‖ww-w‖*‖bb‖+‖bb-b‖ := by rw [norm_mul,norm_mul,hw,one_mul]
      _ ≤ eta*B+eb := by
        have hm := mul_le_mul hww hB (norm_nonneg bb) heta
        linarith
  have hrb : ‖r-w*b‖ ≤ delta+(eta*B+eb) :=
    (norm_sub_le_norm_sub_add_norm_sub r (ww*bb) (w*b)).trans (add_le_add hr hprod)
  constructor
  · calc
      _ = ‖(aa-a)+(r-w*b)‖ := by congr 1; ring
      _ ≤ ‖aa-a‖+‖r-w*b‖ := norm_add_le _ _
      _ ≤ _ := by linarith
  · calc
      _ = ‖(aa-a)-(r-w*b)‖ := by congr 1; ring
      _ ≤ ‖aa-a‖+‖r-w*b‖ := norm_sub_le _ _
      _ ≤ _ := by linarith

/-- Four separately rounded real products incur at most four real ulps in
complex norm. This is the conservative bound requested by the actual C port. -/
theorem complex_four_product_rounding (a b : ℂ) (r0 r1 r2 r3 delta : ℝ)
    (h0 : |r0-a.re*b.re|≤delta) (h1 : |r1-a.im*b.im|≤delta)
    (h2 : |r2-a.re*b.im|≤delta) (h3 : |r3-a.im*b.re|≤delta) :
    ‖(⟨r0-r1,r2+r3⟩ : ℂ)-a*b‖ ≤ 4*delta := by
  have hr : |((⟨r0-r1,r2+r3⟩ : ℂ)-a*b).re| ≤ 2*delta := by
    change |r0-r1-(a.re*b.re-a.im*b.im)| ≤ 2*delta
    have ht := abs_sub (r0-a.re*b.re) (r1-a.im*b.im)
    have he : r0-r1-(a.re*b.re-a.im*b.im) =
      (r0-a.re*b.re)-(r1-a.im*b.im) := by ring
    rw [he]
    linarith
  have hi : |((⟨r0-r1,r2+r3⟩ : ℂ)-a*b).im| ≤ 2*delta := by
    change |r2+r3-(a.re*b.im+a.im*b.re)| ≤ 2*delta
    have ht := abs_add_le (r2-a.re*b.im) (r3-a.im*b.re)
    have he : r2+r3-(a.re*b.im+a.im*b.re) =
      (r2-a.re*b.im)+(r3-a.im*b.re) := by ring
    rw [he]
    linarith
  exact (Complex.norm_le_abs_re_add_abs_im _).trans (by linarith)

/-- A rounded twiddle step has a stable norm-error recurrence when its exact
counterpart is multiplication by a unit complex number. -/
theorem twiddle_step_error (w w0 z z0 r : ℂ) (e eta delta : ℝ)
    (hz : ‖z-z0‖≤e) (hw : ‖w-w0‖≤eta) (hunit : ‖w0‖=1)
    (hzunit : ‖z0‖=1) (heta : 0≤eta) (hr : ‖r-w*z‖≤delta) :
    ‖r-w0*z0‖ ≤ (1+eta)*e+eta+delta := by
  have hnorm : ‖z‖≤e+1 := by
    have h := norm_le_norm_sub_add z z0
    rw [hzunit] at h
    linarith
  have hp : ‖w*z-w0*z0‖≤eta*(e+1)+e := by
    calc
      _ = ‖(w-w0)*z+w0*(z-z0)‖ := by congr 1; ring
      _ ≤ ‖(w-w0)*z‖+‖w0*(z-z0)‖ := norm_add_le _ _
      _ = ‖w-w0‖*‖z‖+‖z-z0‖ := by rw [norm_mul,norm_mul,hunit,one_mul]
      _ ≤ _ := by
        have h := mul_le_mul hw hnorm (norm_nonneg z) heta
        linarith
  have ht := norm_sub_le_norm_sub_add_norm_sub r (w*z) (w0*z0)
  linarith

/-- A mass-sensitive binary-tree roundoff budget. Taking q=(1+eta)^s and
n=2^s yields the next FFT-stage bound, without multiplying the twiddle error by
a uniform bound for all the zero-filled input cells. -/
theorem binary_mass_roundoff_budget (q n ma mb ea eb eta delta : ℝ)
    (hq : 1≤q) (hn : 1≤n) (hma : 0≤ma) (hmb : 0≤mb)
    (heta : 0≤eta) (hd : 0≤delta)
    (ha : ea≤(q-1)*ma+(n-1)*q*delta)
    (hb : eb≤(q-1)*mb+(n-1)*q*delta) :
    ea+(1+eta)*eb+eta*mb+delta ≤
      ((1+eta)*q-1)*(ma+mb)+(2*n-1)*((1+eta)*q)*delta := by
  have heb := mul_le_mul_of_nonneg_left hb (show 0≤1+eta by linarith)
  have h0 : 0≤eta*q*ma := by positivity
  have h1 : 0≤delta*(q-1) := mul_nonneg hd (by linarith)
  have h2 : 0≤n*eta*q*delta := by positivity
  nlinarith

def negativeRoot (n : ℕ) : ℂ :=
  Complex.exp (-2*(Real.pi : ℂ)*Complex.I/(n : ℂ))

lemma negativeRoot_norm (n : ℕ) : ‖negativeRoot n‖=1 := by
  simp [negativeRoot, Complex.norm_exp, Complex.div_re, Complex.mul_re]

lemma negativeRoot_half_power (n : ℕ) (hn : 0<n) :
    negativeRoot (2*n)^n=-1 := by
  have hnc : (n : ℂ)≠0 := by exact_mod_cast hn.ne'
  unfold negativeRoot
  rw [← Complex.exp_nat_mul]
  have he : (n : ℂ)*(-2*(Real.pi : ℂ)*Complex.I/(2*n : ℕ)) =
      -(Real.pi : ℂ)*Complex.I := by
    push_cast
    field_simp <;> ring
  rw [he]
  rw [show -(Real.pi : ℂ)*Complex.I = -(Real.pi*Complex.I) by ring,
    Complex.exp_neg, Complex.exp_pi_mul_I]
  norm_num

lemma negativeRoot_square (n : ℕ) : negativeRoot (2*n)^2=negativeRoot n := by
  unfold negativeRoot
  rw [← Complex.exp_nat_mul]
  congr 1
  by_cases hn : n=0
  · subst n; norm_num
  · have hnc : (n : ℂ)≠0 := by exact_mod_cast hn
    push_cast
    field_simp <;> ring

/-- An executable mathematical radix-two specification, separate from C.
The actual source loop/recursive-call simulation is an additional obligation. -/
def recursiveFFT : ℕ → (ℕ → ℂ) → ℕ → ℂ
  | 0, f, _ => f 0
  | s+1, f, k =>
    let n := 2^s
    if k<n then
      recursiveFFT s (fun j => f (2*j)) k +
        negativeRoot (2*n)^k*recursiveFFT s (fun j => f (2*j+1)) k
    else
      recursiveFFT s (fun j => f (2*j)) (k-n) -
        negativeRoot (2*n)^(k-n)*recursiveFFT s (fun j => f (2*j+1)) (k-n)

/-- Exact correctness of the mathematical recursive FFT for actual complex
negative roots of unity, not merely an arbitrary twiddle satisfying a premise. -/
theorem recursiveFFT_eq_dft (s : ℕ) (f : ℕ → ℂ) (k : ℕ) (hk : k<2^s) :
    recursiveFFT s f k = dftSum (2^s) k (negativeRoot (2^s)) f := by
  induction s generalizing f k with
  | zero =>
    have hk0 : k=0 := by norm_num at hk; omega
    subst k
    simp [recursiveFFT,dftSum]
  | succ s ih =>
    have hlen : (2:ℕ)^(s+1)=2*(2^s) := by rw [pow_succ, Nat.mul_comm]
    by_cases hh : k<2^s
    · rw [recursiveFFT, if_pos hh, ih _ _ hh, ih _ _ hh, hlen]
      exact (by simpa only [negativeRoot_square] using
        (dft_even_odd (2^s) k (negativeRoot (2*2^s)) f).symm)
    · have hj : k-2^s<2^s := by rw [hlen] at hk; omega
      rw [recursiveFFT, if_neg hh, ih _ _ hj, ih _ _ hj, hlen]
      have h := dft_even_odd_second (2^s) (k-2^s) (negativeRoot (2*2^s)) f
        (negativeRoot_half_power (2^s) (by positivity))
      rw [negativeRoot_square, show k-2^s+2^s=k by omega] at h
      exact h.symm

/-- Exact global-table identity used by a recursive implementation's stride. -/
theorem negativeRoot_product_power (n m : ℕ) (hm : 0<m) :
    negativeRoot (n*m)^m=negativeRoot n := by
  unfold negativeRoot
  rw [← Complex.exp_nat_mul]
  congr 1
  by_cases hn : n=0
  · subst n; simp
  · have hnc : (n:ℂ)≠0 := by exact_mod_cast hn
    have hmc : (m:ℂ)≠0 := by exact_mod_cast hm.ne'
    push_cast
    field_simp <;> ring

/-- A conservative concrete24-stage rounding allowance. The input mass8192
bounds all5039possiblynonzero coefficients of the w4 polynomial using |node|≤1.
The C program adds100units atscale1e16, exactly1e-14. -/
theorem fft24_error_budget :
    (((1+(4/10^20:ℝ))^24-1)*8192 +
      ((2:ℝ)^24-1)*(1+(4/10^20:ℝ))^24*(4/10^36)) ≤ 1/10^14 := by
  norm_num

#print axioms dft_even_odd
#print axioms dft_even_odd_second
#print axioms norm_dft_le_mass
#print axioms butterfly_error
#print axioms complex_four_product_rounding
#print axioms twiddle_step_error
#print axioms binary_mass_roundoff_budget
#print axioms negativeRoot_norm
#print axioms negativeRoot_half_power
#print axioms negativeRoot_square
#print axioms recursiveFFT_eq_dft
#print axioms negativeRoot_product_power
#print axioms fft24_error_budget
end RH080Next.FFT
