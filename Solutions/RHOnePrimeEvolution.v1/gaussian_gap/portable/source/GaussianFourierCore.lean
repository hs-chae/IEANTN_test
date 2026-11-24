import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import GaussianSources

/-! Exact Fourier-polynomial bridge for the actual Gaussian witness.
No transform identity or numerical output is assumed. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
open Real Polynomial MeasureTheory
open scoped FourierTransform
namespace RHOnePrime.GaussianFourier

def scale : ℝ := Real.sqrt Real.pi
def gaussian (x : ℝ) : ℝ := Real.exp (-Real.pi * x^2)
def polyWave (p : ℂ[X]) (x : ℝ) : ℂ :=
  p.eval ((scale*x : ℝ) : ℂ) * (gaussian x : ℂ)

lemma scale_sq : scale^2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
lemma scale_pos : 0 < scale := Real.sqrt_pos.mpr Real.pi_pos

lemma integrable_monomial (n : ℕ) :
    Integrable (fun x : ℝ => (((scale*x : ℝ) : ℂ)^n) * (gaussian x : ℂ)) := by
  have h : Integrable (fun x : ℝ => x^n * gaussian x) := by
    simpa only [gaussian, Real.rpow_natCast] using
      (integrable_rpow_mul_exp_neg_mul_sq Real.pi_pos
        (by linarith [Nat.cast_nonneg (α := ℝ) n] : (-1 : ℝ) < (n : ℝ)))
  convert h.ofReal.const_mul ((scale : ℂ)^n) using 1
  funext x
  push_cast
  simp only [mul_pow]
  exact mul_assoc _ _ _

lemma fourier_gaussian : 𝓕 (fun x : ℝ => (gaussian x : ℂ)) =
    fun x : ℝ => (gaussian x : ℂ) := by
  convert (fourier_gaussian_pi (b := (1 : ℂ)) (by norm_num)) using 1 <;>
    simp [gaussian, Complex.ofReal_exp]

lemma hasDerivAt_polyWave (p : ℂ[X]) (x : ℝ) :
    HasDerivAt (polyWave p)
      ((scale : ℂ) * polyWave (p.derivative - C 2 * X * p) x) x := by
  have hu : HasDerivAt (fun y : ℝ => scale*y) scale x := by
    simpa using (hasDerivAt_id x).const_mul scale
  have hp := ((p.hasDerivAt ((scale*x : ℝ) : ℂ)).comp_ofReal).scomp x hu
  have hg := ((Real.hasDerivAt_exp (-Real.pi * x^2)).comp x
    (((hasDerivAt_id x).pow 2).const_mul (-Real.pi))).ofReal_comp
  have hm : HasDerivAt (polyWave p)
      ((scale : ℂ) * p.derivative.eval (↑(scale*x)) * (gaussian x : ℂ) +
        p.eval (↑(scale*x)) * ((gaussian x : ℂ) * (-Real.pi * (2*x) : ℝ))) x := by
    change HasDerivAt (fun y : ℝ => p.eval (↑(scale*y)) * (gaussian y : ℂ)) _ x
    simpa [polyWave, gaussian, Function.comp_def, smul_eq_mul, mul_assoc] using! hp.mul hg
  convert hm using 1
  simp only [polyWave, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X]
  push_cast
  have hs : (scale : ℂ)^2 = (Real.pi : ℂ) := by exact_mod_cast scale_sq
  linear_combination (-2 * (x : ℂ) * p.eval ((scale : ℂ) * (x : ℂ)) * (↑(gaussian x))) * hs

#print axioms integrable_monomial
#print axioms fourier_gaussian
#print axioms hasDerivAt_polyWave
end RHOnePrime.GaussianFourier
