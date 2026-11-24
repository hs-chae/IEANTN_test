import GaussianFourierPolynomial

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
open Polynomial
namespace RHOnePrime.GaussianFourier

def evenStep (p : ℚ[X]) : ℚ[X] :=
  C (-1/4) * p.derivative.derivative + X*p.derivative + (C (1/2) - X^2)*p

lemma step_step (p : ℂ[X]) :
    step (step p) = C (-1/4) * p.derivative.derivative + X*p.derivative +
      (C (1/2) - X^2)*p := by
  have hi : (C (Complex.I/2) : ℂ[X])^2 = C (-1/4) := by
    rw [← map_pow]
    congr 1
    norm_num [div_pow, Complex.I_sq]
  simp only [step, Polynomial.derivative_mul, Polynomial.derivative_sub,
    Polynomial.derivative_C, Polynomial.derivative_X, zero_mul, zero_add,
    mul_one, one_mul]
  ring_nf
  have hi' : (C (Complex.I*(1/2)) : ℂ[X])^2 = C (-1/4) := by
    simpa only [div_eq_mul_inv, one_mul] using hi
  rw [hi']
  norm_num
  have h2 := congrArg (C : ℂ → ℂ[X]) (show (2 : ℂ)*(1/4)=1/2 by norm_num)
  have h4 := congrArg (C : ℂ → ℂ[X]) (show (4 : ℂ)*(1/4)=1 by norm_num)
  simp only [map_mul, map_ofNat, map_one] at h2 h4
  simp only [map_ofNat]
  linear_combination p*h2 + (X*p.derivative-p*X^2)*h4

lemma step_zero : step 0 = 0 := by simp [step]
lemma step_add (p q : ℂ[X]) : step (p+q) = step p + step q := by
  simp only [step, Polynomial.derivative_add]
  ring

lemma step_step_map (p : ℚ[X]) :
    step (step (p.map (Rat.castHom ℂ))) = (evenStep p).map (Rat.castHom ℂ) := by
  rw [step_step]
  simp [evenStep, Polynomial.derivative_map]

def evenSource : List ℚ → List ℚ
  | [] => []
  | c::cs => c::0::evenSource cs

def evenTransform : List ℚ → ℚ[X]
  | [] => 0
  | c::cs => C c + evenStep (evenTransform cs)

lemma transform_evenSource (cs : List ℚ) :
    transformSource (evenSource cs) = (evenTransform cs).map (Rat.castHom ℂ) := by
  induction cs with
  | nil => simp [evenSource, evenTransform, transformSource]
  | cons c cs ih =>
    simp only [evenSource, transformSource, Rat.cast_zero, map_zero, zero_add]
    rw [ih, step_step_map]
    simp [evenTransform]

lemma transformSource_append_zero (cs : List ℚ) :
    transformSource (cs++[0]) = transformSource cs := by
  induction cs with
  | nil => simp [transformSource, step_zero]
  | cons c cs ih => simp [transformSource, ih]

#print axioms step_step
#print axioms transform_evenSource
end RHOnePrime.GaussianFourier
