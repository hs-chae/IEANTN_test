/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTTwiddleBounds

set_option autoImplicit false
noncomputable section
open Real
open scoped BigOperators
namespace RH080Next.FFT

/-- Sixth-order exponential remainder, specialized to the imaginary axis.
Unlike a fourth-order cosine remainder, it is sufficient for the larger
angle in the locked 2^17 Fap transform. -/
theorem imaginary_exp_sixth_order (x : ℝ) (hx : |x|≤1) :
    |cos x-(1-x^2/2+x^4/24)|≤|x|^6*(7/4320:ℝ) ∧
      |sin x-(x-x^3/6+x^5/120)|≤|x|^6*(7/4320:ℝ) := by
  let z : ℂ := (x:ℂ)*Complex.I
  have hn : ‖z‖=|x| := by simp [z,norm_mul]
  have h := Complex.exp_bound (x := z) (n := 6) (by simpa only [hn] using hx) (by norm_num)
  norm_num [hn] at h
  have hr := (Complex.abs_re_le_norm (Complex.exp z-∑ m ∈ Finset.range 6, z^m/(m.factorial:ℂ))).trans h
  have hi := (Complex.abs_im_le_norm (Complex.exp z-∑ m ∈ Finset.range 6, z^m/(m.factorial:ℂ))).trans h
  have hre : (Complex.exp z-∑ m ∈ Finset.range 6, z^m/(m.factorial:ℂ)).re=
      cos x-(1-x^2/2+x^4/24) := by
    norm_num [z,Finset.sum_range_succ,pow_succ,Complex.exp_re,Complex.mul_re,Complex.mul_im]
    ring
  have him : (Complex.exp z-∑ m ∈ Finset.range 6, z^m/(m.factorial:ℂ)).im=
      sin x-(x-x^3/6+x^5/120) := by
    norm_num [z,Finset.sum_range_succ,pow_succ,Complex.exp_im,Complex.mul_re,Complex.mul_im]
    ring
  exact ⟨by simpa only [hre] using hr,by simpa only [him] using hi⟩

def rootSeed17 : ℂ :=
  ⟨999999998851026827562673307794554109/1000000000000000000000000000000000000,
    -47936899603066884549003990494659/1000000000000000000000000000000000000⟩

private def theta17 : ℝ := 2*π/131072

private theorem theta17_bounds :
    (2*3.14159265358979323846/131072:ℝ)≤theta17 ∧
      theta17≤(2*3.14159265358979323847/131072:ℝ) := by
  dsimp [theta17]
  constructor <;> linarith [pi_gt_d20,pi_lt_d20]

theorem rootSeed17_error : ‖rootSeed17-negativeRoot 131072‖≤
    (13/100000000000000000000000000:ℝ) := by
  have ht := theta17_bounds
  have hsmall : 0≤theta17 ∧ theta17≤(5/100000:ℝ) := by constructor <;> linarith
  have hpow (n : ℕ) :
      (2*3.14159265358979323846/131072:ℝ)^n≤theta17^n ∧
        theta17^n≤(2*3.14159265358979323847/131072:ℝ)^n :=
    ⟨pow_le_pow_left₀ (by norm_num) ht.1 n,pow_le_pow_left₀ hsmall.1 ht.2 n⟩
  have hpolyre : |rootSeed17.re-(1-theta17^2/2+theta17^4/24)|≤
      (1/10000000000000000000000000000:ℝ) := by
    have h2 := hpow 2; have h4 := hpow 4
    rw [abs_le]
    norm_num [rootSeed17] at *
    constructor <;> nlinarith
  have hpolyim : |rootSeed17.im+(theta17-theta17^3/6+theta17^5/120)|≤
      (12/100000000000000000000000000:ℝ) := by
    have h3 := hpow 3; have h5 := hpow 5
    rw [abs_le]
    norm_num [rootSeed17] at *
    constructor <;> nlinarith
  have happrox := imaginary_exp_sixth_order theta17
    (by rw [abs_of_nonneg hsmall.1]; linarith)
  rw [abs_of_nonneg hsmall.1] at happrox
  have herr : theta17^6*(7/4320:ℝ)≤(1/10000000000000000000000000000:ℝ) := by
    have h6 := pow_le_pow_left₀ hsmall.1 hsmall.2 6
    nlinarith
  have hre : |rootSeed17.re-cos theta17|≤(2/10000000000000000000000000000:ℝ) := by
    have h := abs_sub_le rootSeed17.re (1-theta17^2/2+theta17^4/24) (cos theta17)
    rw [abs_sub_comm (1-theta17^2/2+theta17^4/24)] at h
    linarith [happrox.1]
  have him : |rootSeed17.im+sin theta17|≤(1201/10000000000000000000000000000:ℝ) := by
    have h := abs_add_le (rootSeed17.im+(theta17-theta17^3/6+theta17^5/120))
      (sin theta17-(theta17-theta17^3/6+theta17^5/120))
    have he : rootSeed17.im+(theta17-theta17^3/6+theta17^5/120)+
      (sin theta17-(theta17-theta17^3/6+theta17^5/120))=rootSeed17.im+sin theta17 := by ring
    rw [he] at h
    linarith [happrox.2]
  have hr : (negativeRoot 131072).re=cos theta17 := by
    simp [negativeRoot,Complex.exp_re,Complex.mul_re,Complex.mul_im,theta17,neg_div]
  have hi : (negativeRoot 131072).im= -sin theta17 := by
    simp [negativeRoot,Complex.exp_im,Complex.mul_re,Complex.mul_im,theta17,neg_div]
  have h := Complex.norm_le_abs_re_add_abs_im (rootSeed17-negativeRoot 131072)
  simp only [Complex.sub_re,Complex.sub_im,hr,hi,sub_neg_eq_add] at h
  exact h.trans (by linarith)

theorem fft17_twiddle_bound (z : ℕ → ℂ) (hz : z 0=1)
    (hstep : ∀ j<65536, ‖z (j+1)-rootSeed17*z j‖≤
      (4/1000000000000000000000000000000000000:ℝ))
    (k : ℕ) (hk : k≤65536) :
    ‖z k-negativeRoot 131072^k‖≤(1/100000000000000000000:ℝ) := by
  have h := repeated_twiddle_error z rootSeed17 (negativeRoot 131072) 65536
    (13/100000000000000000000000000:ℝ)
    (4/1000000000000000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) rootSeed17_error (negativeRoot_norm _) hz hstep k hk
  have hkr : (k:ℝ)≤65536 := by exact_mod_cast hk
  have hg := small_growth_bound (13/100000000000000000000000000:ℝ) (by norm_num) k
    (by linarith : (k:ℝ)*(13/100000000000000000000000000:ℝ)≤1/100)
  have hm := mul_le_mul_of_nonneg_left hg
    (show 0≤(k:ℝ)*((13/100000000000000000000000000:ℝ)+
      4/1000000000000000000000000000000000000) by positivity)
  exact h.trans (by nlinarith)

#print axioms imaginary_exp_sixth_order
#print axioms rootSeed17_error
#print axioms fft17_twiddle_bound
end RH080Next.FFT
