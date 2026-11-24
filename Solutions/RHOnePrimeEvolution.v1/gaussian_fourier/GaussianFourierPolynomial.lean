import GaussianFourierCore

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
open Real Polynomial MeasureTheory
open scoped FourierTransform
namespace RHOnePrime.GaussianFourier

lemma fourier_const_mul (a : ℂ) (f : ℝ → ℂ) :
    𝓕 (fun x => a*f x) = fun y => a * 𝓕 f y := by
  ext y
  simp only [fourier_real_eq_integral_exp_smul, smul_eq_mul]
  simp_rw [mul_left_comm _ a]
  exact integral_const_mul a _

lemma fourier_add {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) :
    𝓕 (fun x => f x + g x) = fun y => 𝓕 f y + 𝓕 g y := by
  ext y
  simp only [fourier_eq, smul_add]
  exact integral_add ((fourierIntegral_convergent_iff y).2 hf)
    ((fourierIntegral_convergent_iff y).2 hg)

def step (p : ℂ[X]) : ℂ[X] := C (Complex.I/2) * (p.derivative - C 2 * X * p)

lemma fourier_mul_coordinate {f : ℝ → ℂ} {p : ℂ[X]}
    (hf : Integrable f) (hxf : Integrable (fun x : ℝ => x • f x))
    (hF : 𝓕 f = polyWave p) :
    𝓕 (fun x : ℝ => ((scale*x : ℝ) : ℂ) * f x) = polyWave (step p) := by
  have hd := Real.deriv_fourier hf hxf
  rw [hF] at hd
  have hmul : (fun x : ℝ => (-2*Real.pi*Complex.I*x) • f x) =
      fun x : ℝ => (-2*(scale : ℂ)*Complex.I) * (((scale*x : ℝ) : ℂ)*f x) := by
    funext x
    simp only [smul_eq_mul, Complex.ofReal_mul]
    have hs : (scale : ℂ)^2 = (Real.pi : ℂ) := by exact_mod_cast scale_sq
    linear_combination (2*Complex.I*(x : ℂ)*f x) * hs
  rw [hmul, fourier_const_mul] at hd
  funext x
  have he := congrFun hd x
  rw [(hasDerivAt_polyWave p x).deriv] at he
  have hn : (-2*(scale : ℂ)*Complex.I) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr scale_pos.ne'))
      Complex.I_ne_zero
  apply (mul_left_cancel₀ hn)
  rw [← he]
  simp only [step, polyWave, Polynomial.eval_mul, Polynomial.eval_C]
  have hi := Complex.I_sq
  linear_combination (scale : ℂ) *
    (p.derivative - C 2 * X * p).eval (↑(scale*x)) * (gaussian x : ℂ) * hi

open RHOnePrime.GaussianKernel
def sourceWave (cs : List ℚ) (x : ℝ) : ℂ :=
  (coeffEval cs (scale*x) : ℂ) * (gaussian x : ℂ)

lemma sourceWave_cons (c : ℚ) (cs : List ℚ) :
    sourceWave (c::cs) = fun x : ℝ =>
      (c : ℂ)*(gaussian x : ℂ) + ((scale*x : ℝ) : ℂ)*sourceWave cs x := by
  funext x
  simp only [sourceWave, coeffEval, Complex.ofReal_add, Complex.ofReal_mul,
    Complex.ofReal_ratCast]
  ring

lemma integrable_source_moment (cs : List ℚ) (n : ℕ) :
    Integrable (fun x : ℝ => (((scale*x : ℝ) : ℂ)^n) * sourceWave cs x) := by
  induction cs generalizing n with
  | nil => simp [sourceWave, coeffEval]
  | cons c cs ih =>
    have h := ((integrable_monomial n).const_mul (c : ℂ)).add (ih (n+1))
    convert! h using 1
    funext x
    rw [sourceWave_cons]
    simp only [pow_succ, Pi.add_apply]
    ring

lemma integrable_sourceWave (cs : List ℚ) : Integrable (sourceWave cs) := by
  simpa using integrable_source_moment cs 0

lemma integrable_coordinate_sourceWave (cs : List ℚ) :
    Integrable (fun x : ℝ => x • sourceWave cs x) := by
  have h := (integrable_source_moment cs 1).const_mul ((scale : ℂ)⁻¹)
  convert! h using 1
  funext x
  simp only [pow_one, RCLike.real_smul_eq_coe_mul, Complex.ofReal_mul]
  have hn : (scale : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr scale_pos.ne'
  field_simp
  exact mul_comm _ _

def transformSource : List ℚ → ℂ[X]
  | [] => 0
  | c::cs => C (c : ℂ) + step (transformSource cs)

theorem fourier_sourceWave (cs : List ℚ) :
    𝓕 (sourceWave cs) = polyWave (transformSource cs) := by
  induction cs with
  | nil =>
    ext x
    simp [sourceWave, coeffEval, transformSource, polyWave, fourier_eq]
  | cons c cs ih =>
    have hg : Integrable (fun x : ℝ => (c : ℂ)*(gaussian x : ℂ)) := by
      simpa only [gaussian] using!
        ((integrable_exp_neg_mul_sq Real.pi_pos).ofReal.const_mul (c : ℂ))
    have hu : Integrable (fun x : ℝ => ((scale*x : ℝ) : ℂ)*sourceWave cs x) := by
      simpa using integrable_source_moment cs 1
    rw [sourceWave_cons, fourier_add hg hu, fourier_const_mul, fourier_gaussian]
    rw [fourier_mul_coordinate (integrable_sourceWave cs)
      (integrable_coordinate_sourceWave cs) ih]
    funext x
    simp only [transformSource, polyWave, Polynomial.eval_add, Polynomial.eval_C]
    ring

#print axioms fourier_mul_coordinate
#print axioms integrable_sourceWave
#print axioms fourier_sourceWave
end RHOnePrime.GaussianFourier
