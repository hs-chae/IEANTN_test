/- Poststudy integration of unchanged H02-STRUCTURED. The psi input is discharged
from the same actual C source-main physical total read, with all fourteen inputs. -/
import SynergyHeightC.MainPiPsi300Read
import Main
namespace SynergyHeightC.ThetaRead300
open ScopedC ScopedC.Machine ScopedNumerical SynergyBasis ScopedIO
open Real IEANTN WinnerOriginalScalars WinnerNewHeightSource WinnerDirectKernel
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 100000

theorem psi_alias : ExposureTask.Epsi = IEANTN.Eψ := rfl
theorem theta_alias : ExposureTask.Etheta = IEANTN.Eθ := rfl

theorem from_actual_total_read
    {out : ProofBox}
    (read : evalExpr SynergyC.Header.layout FullMainPrefix.service 1
      (FullMainEdges.loopState (SourceMainBudgetV1.Data.total 768) 768) (.var "total")=
      some (SynergyC.SourceIntervalMath.represented out,
        FullMainEdges.loopState (SourceMainBudgetV1.Data.total 768) 768))
    (h : PrimaryInputs (3681/10000) (3599/10000))
    (hCHJ : OriginalCHJSource) (hrvm : ZeroCount.v1.rvm_error_bound)
    (hsmall : ZeroCount.v1.rvm_error_small)
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    (hRH : RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH : ZetaZeroFreeHalfPlane (7/8)) {x : ℝ} (hx : Real.exp 300 ≤ x) :
    Eθ x ≤ (9354674/1000000000:ℝ)*x^(-(1:ℝ)/8)+(2*Real.sqrt x*Real.log x)/x ∧
    Eθ x ≤ ((9354674/1000000000:ℝ)+16/Real.exp 75)*x^(-(1:ℝ)/8) ∧
    Eθ x ≤ ((9354674/1000000000:ℝ)+1/1000000000)*x^(-(1:ℝ)/8) := by
  have ray := (MainPiPsi300Read.pi_psi_300_from_actual_total_read read
    h hCHJ hrvm hsmall hlow hRH hQRH).2
  have input : ∀ t : ℝ, Real.exp 300 ≤ t →
      ExposureTask.Epsi t ≤ ExposureTask.C*t^(-(1:ℝ)/8) := by
    intro t ht
    change IEANTN.Eψ t ≤ (9354674/1000000000:ℝ)*t^(-(1:ℝ)/8)
    simpa only [pow_zero,mul_one,show (7/8:ℝ)-1= -1/8 by norm_num] using ray t ht
  exact ⟨by simpa only [theta_alias,ExposureTask.C] using ExposureTask.theta_two_term input hx,
    by simpa only [theta_alias,ExposureTask.C] using ExposureTask.theta_transport input hx,
    by simpa only [theta_alias,ExposureTask.C] using ExposureTask.theta_target input hx⟩

#print axioms psi_alias
#print axioms theta_alias
#print axioms from_actual_total_read
end SynergyHeightC.ThetaRead300
