import GaussianRationalTransform
import GaussianPhysical

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Polynomial
namespace RHOnePrime.GaussianFourier
open RHOnePrime.GaussianKernel

/-- Actual even-index coefficients of normSource; the exact association below
is kernel-checked against the original source list. -/
def normEvenSource : List ℚ := [(419430399999999148579364/419430400000000000000000 : ℚ), (-16126343823867693898751/26214400000000000000000 : ℚ), (-2150875416409801956899/13107200000000000000000 : ℚ), (155637771812266820413/4915200000000000000000 : ℚ), (19362734561153602301/1638400000000000000000 : ℚ), (-98798297423234449/30720000000000000000 : ℚ), (2797684222170260383/1152000000000000000000 : ℚ), (-930110400097128511/1008000000000000000000 : ℚ), (393586652355322367/2016000000000000000000 : ℚ), (-3335144852742113/126000000000000000000 : ℚ), (2004300872712673/945000000000000000000 : ℚ), (-339804333794473/3898125000000000000000 : ℚ), (5431574022383/3898125000000000000000 : ℚ)]

lemma actual_even_expansion : evenSource normEvenSource = normSource++[0] := by
  norm_num [evenSource, normEvenSource, normSource]

/-- Exact rational polynomial calculation; no native execution axiom. -/
lemma actual_even_transform : evenTransform normEvenSource = coeffPoly wingSource := by
  have h : evenTransformCoeffs normEvenSource = wingSource := by decide +kernel
  rw [← coeffPoly_evenTransformCoeffs, h]

#print axioms actual_even_transform
end RHOnePrime.GaussianFourier
