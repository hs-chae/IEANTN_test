import GaussianFourierEven
import GaussianCoeffArithmetic

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
open Polynomial
namespace RHOnePrime.GaussianFourier
open RHOnePrime.GaussianKernel

/-- Reuse the numerical certificate's actual rational arithmetic primitives. -/
abbrev addCoeffs := RHOnePrime.GaussianKernel.coeffAdd
abbrev scaleCoeffs := RHOnePrime.GaussianKernel.coeffScale

def derivativeCoeffs : List ℚ → List ℚ
  | [] => []
  | _::cs => addCoeffs cs (0::derivativeCoeffs cs)

def trimCoeffs : List ℚ → List ℚ
  | [] => []
  | c::cs => let t := trimCoeffs cs; if t=[] ∧ c=0 then [] else c::t

lemma coeffPoly_addCoeffs (cs ds : List ℚ) :
    coeffPoly (addCoeffs cs ds) = coeffPoly cs + coeffPoly ds := by
  induction cs generalizing ds with
  | nil => simp [addCoeffs, coeffAdd, coeffPoly]
  | cons c cs ih =>
    cases ds with
    | nil => simp [addCoeffs, coeffAdd, coeffPoly]
    | cons d ds => simp [addCoeffs, coeffAdd, coeffPoly, ih]; ring

lemma coeffPoly_scaleCoeffs (a : ℚ) (cs : List ℚ) :
    coeffPoly (scaleCoeffs a cs) = C a * coeffPoly cs := by
  induction cs with
  | nil => simp [scaleCoeffs, coeffScale, coeffPoly]
  | cons c cs ih => simp [scaleCoeffs, coeffScale, coeffPoly] at ih ⊢; rw [ih]; ring

lemma coeffPoly_derivativeCoeffs (cs : List ℚ) :
    coeffPoly (derivativeCoeffs cs) = (coeffPoly cs).derivative := by
  induction cs with
  | nil => simp [derivativeCoeffs, coeffPoly]
  | cons c cs ih =>
    simp [derivativeCoeffs, coeffPoly_addCoeffs, coeffPoly, ih]

lemma coeffPoly_trimCoeffs (cs : List ℚ) : coeffPoly (trimCoeffs cs) = coeffPoly cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [trimCoeffs]
    split_ifs with h
    · have he : coeffPoly cs = 0 := by rw [← ih, h.1]; rfl
      simp [coeffPoly, h.2, he]
    · simp [coeffPoly, ih]

def evenStepCoeffs (cs : List ℚ) : List ℚ :=
  addCoeffs (scaleCoeffs (-1/4) (derivativeCoeffs (derivativeCoeffs cs)))
    (addCoeffs (0::derivativeCoeffs cs)
      (addCoeffs (scaleCoeffs (1/2) cs) (0::0::scaleCoeffs (-1) cs)))

lemma coeffPoly_evenStepCoeffs (cs : List ℚ) :
    coeffPoly (evenStepCoeffs cs) = evenStep (coeffPoly cs) := by
  simp only [evenStepCoeffs, coeffPoly_addCoeffs, coeffPoly_scaleCoeffs,
    coeffPoly_derivativeCoeffs, coeffPoly, map_zero, zero_add, evenStep,
    map_neg, map_one]
  ring

def evenTransformCoeffs : List ℚ → List ℚ
  | [] => []
  | c::cs => trimCoeffs (addCoeffs [c] (evenStepCoeffs (evenTransformCoeffs cs)))

theorem coeffPoly_evenTransformCoeffs (cs : List ℚ) :
    coeffPoly (evenTransformCoeffs cs) = evenTransform cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp [evenTransformCoeffs, coeffPoly_trimCoeffs, coeffPoly_addCoeffs,
      coeffPoly_evenStepCoeffs, ih, evenTransform, coeffPoly]

#print axioms coeffPoly_evenTransformCoeffs
end RHOnePrime.GaussianFourier
