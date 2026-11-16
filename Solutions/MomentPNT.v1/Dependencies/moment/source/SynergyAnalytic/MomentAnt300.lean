/- Shared analytic consumer of a genuinely supplied numerical moment budget.
This changes no analytic source assumption and works equally for kernel-only and
source-first providers. It does not supply either numerical provider by itself. -/
import SynergyAnalytic.MomentPNTTransfer
namespace SynergyAnalytic
open Real IEANTN WinnerOriginalScalars WinnerNewHeightSource WinnerDirectKernel
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 100000

theorem pi_300_from_moment_budget {a c D : Nat→ℝ} {n : Nat} {B : ℝ}
 (monotone : Monotone a) (first : a 0=WinnerOriginalScalars.height)
 (last : a n=Real.exp 60)
 (budget : spectralBase 300 100+profileCoefficient a c D n 300 ≤ B)
 (caps : ActualHeightCaps a c D n)
 (h : PrimaryInputs (3681/10000) (3599/10000))
 (hCHJ : OriginalCHJSource) (hrvm : ZeroCount.v1.rvm_error_bound)
 (hsmall : ZeroCount.v1.rvm_error_small)
 (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
 (hRH : RiemannHypothesisUpTo WinnerOriginalScalars.height)
 (hQRH : ZetaZeroFreeHalfPlane (7/8)) :
 HasPowerLogBound Eπ ((1+1/1000000000)*B+1/1000000000000+1/100000000)
  0 (7/8) (Real.exp 300) :=
 rh_pi_ray_of_budgets hCHJ hQRH hlow (by norm_num : (300:ℝ) ≤ 300)
  (fun L future=>raw_ray300_of_budget monotone first last budget h caps
    hrvm hsmall hlow hRH hQRH future)
  (fun L future=>low_paired_kernel_tiny hQRH hRH hrvm hsmall hlow future)

theorem psi_300_from_moment_budget {a c D : Nat→ℝ} {n : Nat} {B : ℝ}
 (monotone : Monotone a) (first : a 0=WinnerOriginalScalars.height)
 (last : a n=Real.exp 60)
 (budget : spectralBase 300 100+profileCoefficient a c D n 300 ≤ B)
 (caps : ActualHeightCaps a c D n)
 (h : PrimaryInputs (3681/10000) (3599/10000))
 (hCHJ : OriginalCHJSource) (hrvm : ZeroCount.v1.rvm_error_bound)
 (hsmall : ZeroCount.v1.rvm_error_small)
 (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
 (hRH : RiemannHypothesisUpTo WinnerOriginalScalars.height)
 (hQRH : ZetaZeroFreeHalfPlane (7/8)) :
 HasPowerLogBound Eψ (B+1/100000000) 0 (7/8) (Real.exp 300) := by
 intro x hx
 have positiveX : 0 < x:=(Real.exp_pos 300).trans_le hx
 let L:=Real.log x
 have future : 300 ≤ L := by
  have q:=Real.log_le_log (Real.exp_pos 300) hx
  simpa only [Real.log_exp] using q
 have raw:=raw_ray300_of_budget monotone first last budget h caps
   hrvm hsmall hlow hRH hQRH future
 have normalized:=direct_psi_normalized_of_raw hCHJ hQRH hlow future raw
 have heq : Real.exp L=x:=Real.exp_log positiveX
 have bound : Eψ (Real.exp L) ≤ (B+1/100000000)*Real.exp (-L/8) := by
  have inverse : Real.exp (-L/8)=1/Real.exp (L/8) := by
   rw [show -L/8= -(L/8) by ring,Real.exp_neg,one_div]
  rw [inverse,mul_one_div]
  exact (le_div_iff₀ (Real.exp_pos _)).mpr normalized
 rw [heq] at bound
 have power : x^(-(1:ℝ)/8)=Real.exp (-L/8) := by
  rw [Real.rpow_def_of_pos positiveX]
  dsimp only [L]
  congr 1
  ring
 simp only [pow_zero,mul_one,show (7/8:ℝ)-1= -1/8 by norm_num]
 rw [power]
 exact bound
#print axioms pi_300_from_moment_budget
#print axioms psi_300_from_moment_budget
end SynergyAnalytic
