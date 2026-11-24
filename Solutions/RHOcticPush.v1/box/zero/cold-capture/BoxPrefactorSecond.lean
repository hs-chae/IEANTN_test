import BoxPrefactor
import BoxGammaRealSecond

/-! The actual second derivative of the Box Mellin prefactor. -/
namespace RHOcticPush.BoxGamma
open Real Filter Set
open scoped Topology

private noncomputable def num (s : ℝ) := (2 : ℝ)^(-s)
private noncomputable def den (s : ℝ) :=
  Real.Gamma (2 - s) * Real.cos (Real.pi * s / 2)
private noncomputable def numD (s : ℝ) := -Real.log 2 * num s
private noncomputable def denD (s : ℝ) :=
  -(deriv Real.Gamma (2 - s) * Real.cos (Real.pi * s / 2)) -
    Real.Gamma (2 - s) * Real.sin (Real.pi * s / 2) * (Real.pi / 2)

private lemma num_derivative (s : ℝ) : HasDerivAt num (numD s) s := by
  have hd := HasDerivAt.const_rpow (show (0 : ℝ) < 2 by norm_num)
    ((hasDerivAt_id s).neg)
  exact hd.congr_deriv (by dsimp [numD, num]; ring)

private lemma den_derivative {s : ℝ} (hs : s < 2) : HasDerivAt den (denD s) s := by
  have hg0 := (Real.differentiableAt_Gamma (s := 2 - s) (by
    intro n hn
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith)).hasDerivAt
  have hg := hg0.comp s ((hasDerivAt_id s).const_sub 2)
  have hc := (((hasDerivAt_id s).const_mul Real.pi).div_const 2).cos
  exact (hg.mul hc).congr_deriv (by dsimp [denD]; ring)

private lemma num_zero : num 0 = 1 := by norm_num [num]
private lemma den_zero : den 0 = 1 := by
  norm_num [den, Real.Gamma_nat_eq_factorial]
private lemma numD_zero : numD 0 = -Real.log 2 := by simp [numD, num_zero]
private lemma denD_zero : denD 0 = Real.eulerMascheroniConstant - 1 := by
  norm_num [denD, gamma_two_derivative.deriv]

private lemma numD_derivative : HasDerivAt numD ((Real.log 2)^2) 0 := by
  exact ((num_derivative 0).const_mul (-Real.log 2)).congr_deriv
    (by rw [numD_zero]; ring)

private lemma denD_derivative : HasDerivAt denD
    (Real.eulerMascheroniConstant^2 - 2 * Real.eulerMascheroniConstant -
      Real.pi^2 / 12) 0 := by
  have hg0 : HasDerivAt Real.Gamma (1 - Real.eulerMascheroniConstant)
      (2 - (0 : ℝ)) := by simpa using gamma_two_derivative
  have hg := hg0.comp 0 ((hasDerivAt_id (0 : ℝ)).const_sub 2)
  have hg20 : HasDerivAt (deriv Real.Gamma)
      (Real.eulerMascheroniConstant^2 - 2 * Real.eulerMascheroniConstant +
        Real.pi^2 / 6) (2 - (0 : ℝ)) := by simpa using gamma_real_second_two
  have hg2 := hg20.comp 0 ((hasDerivAt_id (0 : ℝ)).const_sub 2)
  have hangle := ((hasDerivAt_id (0 : ℝ)).const_mul Real.pi).div_const 2
  have hc := hangle.cos
  have hs := hangle.sin
  have hd := (hg2.mul hc).neg.sub ((hg.mul hs).mul_const (Real.pi / 2))
  exact hd.congr_deriv (by norm_num [Real.Gamma_nat_eq_factorial]; ring)

private noncomputable def quotientD (s : ℝ) :=
  (numD s * den s - num s * denD s) / (den s)^2

private lemma quotientD_derivative : HasDerivAt quotientD
    ((1 - Real.eulerMascheroniConstant - Real.log 2)^2 + 1 + Real.pi^2 / 12) 0 := by
  have hn := num_derivative 0
  have hd := den_derivative (show (0 : ℝ) < 2 by norm_num)
  have htop := (numD_derivative.mul hd).sub (hn.mul denD_derivative)
  have hq := htop.div (hd.pow 2) (by change den 0 ^ 2 ≠ 0; rw [den_zero]; norm_num)
  exact hq.congr_deriv (by
    dsimp only [Pi.pow_apply, Pi.sub_apply, Pi.mul_apply]
    rw [num_zero, den_zero, numD_zero, denD_zero]
    ring)

theorem prefactor_second : HasDerivAt (deriv prefactor)
    ((1 - Real.eulerMascheroniConstant - Real.log 2)^2 + 1 + Real.pi^2 / 12) 0 := by
  have he0 : ∀ᶠ s : ℝ in 𝓝 0, den s ≠ 0 :=
    (den_derivative (show (0 : ℝ) < 2 by norm_num)).continuousAt.eventually_ne
      (by rw [den_zero]; norm_num)
  apply quotientD_derivative.congr_of_eventuallyEq
  filter_upwards [he0, Iio_mem_nhds (show (0 : ℝ) < 2 by norm_num)] with s hs hs2
  exact ((num_derivative s).div (den_derivative hs2) hs).deriv

#print axioms prefactor_second
end RHOcticPush.BoxGamma
