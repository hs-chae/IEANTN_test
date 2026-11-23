import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

/-! Actual scalar derivative in the Box Mellin factorization. -/
namespace RHOcticPush.BoxGamma
open Real Filter Set
open scoped Topology

/-- The actual scalar multiplying the zeta/regular-series expression. -/
noncomputable def prefactor (s : ℝ) : ℝ :=
  (2 : ℝ) ^ (-s) / (Real.Gamma (2 - s) * Real.cos (Real.pi * s / 2))

lemma gamma_two_derivative :
    HasDerivAt Real.Gamma (1 - Real.eulerMascheroniConstant) 2 := by
  convert Real.hasDerivAt_Gamma_nat 1 using 1 <;>
    norm_num [harmonic] <;> ring

@[simp] lemma prefactor_zero : prefactor 0 = 1 := by
  norm_num [prefactor, Real.Gamma_nat_eq_factorial]

/-- No moment or zeta-coefficient hypothesis is used in this derivative. -/
theorem prefactor_hasDerivAt : HasDerivAt prefactor
    (1 - Real.eulerMascheroniConstant - Real.log 2) 0 := by
  have hp := HasDerivAt.const_rpow (show (0 : ℝ) < 2 by norm_num)
    ((hasDerivAt_id (0 : ℝ)).neg)
  have hg0 : HasDerivAt Real.Gamma (1 - Real.eulerMascheroniConstant)
      (2 - (0 : ℝ)) := by simpa using gamma_two_derivative
  have hg := hg0.comp 0 ((hasDerivAt_id (0 : ℝ)).const_sub 2)
  have hc := (((hasDerivAt_id (0 : ℝ)).const_mul Real.pi).div_const 2).cos
  have hd := hp.div (hg.mul hc) (by norm_num [Real.Gamma_nat_eq_factorial])
  exact hd.congr_deriv (by norm_num [Real.Gamma_nat_eq_factorial]; ring)

#print axioms gamma_two_derivative
#print axioms prefactor_hasDerivAt
end RHOcticPush.BoxGamma
