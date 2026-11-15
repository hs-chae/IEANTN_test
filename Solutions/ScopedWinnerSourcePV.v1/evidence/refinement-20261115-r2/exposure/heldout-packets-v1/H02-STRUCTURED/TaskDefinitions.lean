import Mathlib
namespace ExposureTask
open Real
noncomputable def Epsi (x : ℝ) : ℝ := |Chebyshev.psi x-x|/x
noncomputable def Etheta (x : ℝ) : ℝ := |Chebyshev.theta x-x|/x
def C : ℝ := 9354674/1000000000
end ExposureTask
