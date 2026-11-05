/- Copyright (c) 2026 IEANTN contributors. Released under Apache2.0. -/
import WinnerDensityA.HeightResult
import StrongFullComparison
import OldC4Upper
namespace WinnerStrongEnvelope
open Real IEANTN Set
set_option maxHeartbeats 0
/-- Actual prime-counting conclusion and strict comparison with the explicit
old allowance functional on a nondegenerate interval. The rival's original
source validity is separately exposed by OldC4Upper.actual_old_moment_at_T
and the original KLN/Rosser/explicit-formula source contracts. -/
theorem actual_prime_comparison
    (hCHJ:WinnerDirectKernel.OriginalCHJSource)
    (hrvm:ZeroCount.v1.rvm_error_bound) (hsmall:ZeroCount.v1.rvm_error_small)
    (hlow:LowZeroes.v1.no_zeroes_below_first_ordinate)
    (h:WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH:RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH:ZetaZeroFreeHalfPlane (7/8)) :
    ∀x∈Icc (exp (300:ℝ)) (exp (30001/100:ℝ)),
      Eπ x ≤ (2371/250000:ℝ)*x^(-(1:ℝ)/8) ∧
      (2371/250000:ℝ)*x^(-(1:ℝ)/8)<oldFullAllowance (log x)*x^(-(1:ℝ)/8) := by
  intro x hx
  have hx0 : 0<x := (exp_pos (300:ℝ)).trans_le hx.1
  have hLower : (300:ℝ) ≤ log x := by
    have hh:=log_le_log (exp_pos (300:ℝ)) hx.1
    simpa only [log_exp] using hh
  have hUpper : log x ≤ (30001/100:ℝ) := by
    have hh:=log_le_log hx0 hx.2
    simpa only [log_exp] using hh
  have hPrime:=WinnerDensityA.HeightFinal.source_pi_009484 hCHJ hrvm hsmall hlow h hRH hQRH x hx.1
  simp only [pow_zero,mul_one] at hPrime
  have he : (7/8:ℝ)-1=-(1:ℝ)/8 := by norm_num
  rw [he] at hPrime
  exact ⟨hPrime,mul_lt_mul_of_pos_right (uniform_coefficient_strict hLower hUpper) (rpow_pos_of_pos hx0 _)⟩
#print axioms actual_prime_comparison
#print actual_prime_comparison
#check WinnerOldC4Upper.actual_old_moment_at_T
end WinnerStrongEnvelope
