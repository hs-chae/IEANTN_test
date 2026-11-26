/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTButterfly

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace RH080Next.FFT

def coefficientMass (n : ℕ) (f : ℕ → ℂ) : ℝ :=
  ∑ j ∈ Finset.range n, ‖f j‖

lemma coefficientMass_nonneg (n : ℕ) (f : ℕ → ℂ) : 0≤coefficientMass n f :=
  Finset.sum_nonneg (fun _ _ => norm_nonneg _)

lemma coefficientMass_double (n : ℕ) (f : ℕ → ℂ) :
    coefficientMass (2*n) f = coefficientMass n (fun j => f (2*j)) +
      coefficientMass n (fun j => f (2*j+1)) := by
  unfold coefficientMass
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2*(n+1)=2*n+1+1 by omega, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, Finset.sum_range_succ, Finset.sum_range_succ]
    ring

/-- A mathematical fixed-point FFT specification. The rounding callback and
twiddle table will be refined by the actual source; this definition alone is
neither an execution of C nor source-first PV. -/
def roundedFFT (w : ℕ → ℕ → ℂ) (mul : ℂ → ℂ → ℂ) :
    ℕ → (ℕ → ℂ) → ℕ → ℂ
  | 0, f, _ => f 0
  | s+1, f, k =>
    let n := 2^s
    let j := if k<n then k else k-n
    let a := roundedFFT w mul s (fun i => f (2*i)) j
    let b := roundedFFT w mul s (fun i => f (2*i+1)) j
    let r := mul (w (s+1) j) b
    if k<n then a+r else a-r

/-- Global pointwise error of the rounded recursive algorithm. The mass term
is the actual coefficient L1 mass; padding the input by zeros does not enlarge
it. The two stated callback properties are mathematical conditions which the
source-verification proof must discharge. -/
theorem roundedFFT_error (s : ℕ) (f : ℕ → ℂ) (k : ℕ) (hk : k<2^s)
    (w : ℕ → ℕ → ℂ) (mul : ℂ → ℂ → ℂ) (eta delta : ℝ)
    (heta : 0≤eta) (hdelta : 0≤delta)
    (hw : ∀ t<s, ∀ j<2^t, ‖w (t+1) j-negativeRoot (2*2^t)^j‖≤eta)
    (hmul : ∀ a b : ℂ, ‖mul a b-a*b‖≤delta) :
    ‖roundedFFT w mul s f k-recursiveFFT s f k‖ ≤
      ((1+eta)^s-1)*coefficientMass (2^s) f +
        ((2:ℝ)^s-1)*(1+eta)^s*delta := by
  induction s generalizing f k with
  | zero => simp [roundedFFT,recursiveFFT]
  | succ s ih =>
    have hlen : (2:ℕ)^(s+1)=2*(2^s) := by rw [pow_succ,Nat.mul_comm]
    have hw' : ∀ t<s, ∀ j<2^t, ‖w (t+1) j-negativeRoot (2*2^t)^j‖≤eta :=
      fun t ht j hj => hw t (by omega) j hj
    have hstep (j : ℕ) (hj : j<2^s) :
        ‖(roundedFFT w mul s (fun i => f (2*i)) j +
          mul (w (s+1) j) (roundedFFT w mul s (fun i => f (2*i+1)) j)) -
          (recursiveFFT s (fun i => f (2*i)) j +
            negativeRoot (2*2^s)^j*recursiveFFT s (fun i => f (2*i+1)) j)‖ ≤
          ((1+eta)^(s+1)-1)*coefficientMass (2^(s+1)) f+
            ((2:ℝ)^(s+1)-1)*(1+eta)^(s+1)*delta ∧
        ‖(roundedFFT w mul s (fun i => f (2*i)) j -
          mul (w (s+1) j) (roundedFFT w mul s (fun i => f (2*i+1)) j)) -
          (recursiveFFT s (fun i => f (2*i)) j -
            negativeRoot (2*2^s)^j*recursiveFFT s (fun i => f (2*i+1)) j)‖ ≤
          ((1+eta)^(s+1)-1)*coefficientMass (2^(s+1)) f+
            ((2:ℝ)^(s+1)-1)*(1+eta)^(s+1)*delta := by
      let a := recursiveFFT s (fun i => f (2*i)) j
      let b := recursiveFFT s (fun i => f (2*i+1)) j
      let aa := roundedFFT w mul s (fun i => f (2*i)) j
      let bb := roundedFFT w mul s (fun i => f (2*i+1)) j
      let ea := ‖aa-a‖
      let eb := ‖bb-b‖
      let ma := coefficientMass (2^s) (fun i => f (2*i))
      let mb := coefficientMass (2^s) (fun i => f (2*i+1))
      have ha := ih (fun i => f (2*i)) j hj hw'
      have hb := ih (fun i => f (2*i+1)) j hj hw'
      have hbmass : ‖b‖≤mb := by
        dsimp [b,mb]
        rw [recursiveFFT_eq_dft s _ j hj]
        exact norm_dft_le_mass _ _ _ _ (negativeRoot_norm _)
      have hbb : ‖bb‖≤mb+eb := by
        have h := norm_le_norm_sub_add bb b
        dsimp [eb]
        linarith
      have hunit : ‖negativeRoot (2*2^s)^j‖=1 := by
        rw [norm_pow,negativeRoot_norm,one_pow]
      have hbf := butterfly_error a b aa bb (negativeRoot (2*2^s)^j)
        (w (s+1) j) (mul (w (s+1) j) bb) ea eb eta delta (mb+eb)
        le_rfl le_rfl hunit (hw s (by omega) j hj) hbb heta (hmul _ _)
      have hbudget := binary_mass_roundoff_budget ((1+eta)^s) ((2:ℝ)^s)
        ma mb ea eb eta delta
        (one_le_pow₀ (by linarith : (1:ℝ)≤1+eta))
        (one_le_pow₀ (by norm_num : (1:ℝ)≤2))
        (coefficientMass_nonneg _ _) (coefficientMass_nonneg _ _) heta hdelta ha hb
      have hbudget' : ea+eb+eta*(mb+eb)+delta ≤
          ((1+eta)^(s+1)-1)*coefficientMass (2^(s+1)) f+
            ((2:ℝ)^(s+1)-1)*(1+eta)^(s+1)*delta := by
        rw [hlen,coefficientMass_double]
        dsimp [ma,mb] at hbudget
        convert hbudget using 1 <;> (try simp only [pow_succ,ma,mb]) <;> ring
      exact ⟨hbf.1.trans hbudget',hbf.2.trans hbudget'⟩
    by_cases hh : k<2^s
    · simpa [roundedFFT,recursiveFFT,hh] using (hstep k hh).1
    · have hj : k-2^s<2^s := by rw [hlen] at hk; omega
      simpa [roundedFFT,recursiveFFT,hh] using (hstep (k-2^s) hj).2

/-- The source-independent numerical enclosure is directly a bound for the
actual DFT once the callbacks and source simulation have been proved. -/
theorem roundedFFT_dft_error (s : ℕ) (f : ℕ → ℂ) (k : ℕ) (hk : k<2^s)
    (w : ℕ → ℕ → ℂ) (mul : ℂ → ℂ → ℂ) (eta delta : ℝ)
    (heta : 0≤eta) (hdelta : 0≤delta)
    (hw : ∀ t<s, ∀ j<2^t, ‖w (t+1) j-negativeRoot (2*2^t)^j‖≤eta)
    (hmul : ∀ a b : ℂ, ‖mul a b-a*b‖≤delta) :
    ‖roundedFFT w mul s f k-dftSum (2^s) k (negativeRoot (2^s)) f‖ ≤
      ((1+eta)^s-1)*coefficientMass (2^s) f+
        ((2:ℝ)^s-1)*(1+eta)^s*delta := by
  rw [← recursiveFFT_eq_dft s f k hk]
  exact roundedFFT_error s f k hk w mul eta delta heta hdelta hw hmul

#print axioms roundedFFT_error
#print axioms roundedFFT_dft_error
end RH080Next.FFT
