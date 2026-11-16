/- Poststudy integration of the unchanged, independently checked H01-PROSE proof.
The actual source-produced total read supplies its sole prime-counting input. -/
import SynergyHeightC.MainPiPsi300Read
import IEANTN.Vocabulary.PrimeReciprocal
import Tail
namespace SynergyHeightC.ReciprocalRead300
open ScopedC ScopedC.Machine ScopedNumerical SynergyBasis ScopedIO
open Real IEANTN WinnerOriginalScalars WinnerNewHeightSource WinnerDirectKernel
open Filter
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 100000

theorem pi_alias : ExposureTask.pi = IEANTN.primeCounting := rfl
theorem li_alias : ExposureTask.Li2 = IEANTN.Li := rfl
theorem error_alias : ExposureTask.Epi = IEANTN.Eπ := rfl
theorem reciprocal_alias : ExposureTask.primeReciprocal = IEANTN.primeReciprocal := rfl

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
    (hQRH : ZetaZeroFreeHalfPlane (7/8)) :
    ∃ B : ℝ,
      Tendsto (fun x : ℝ => IEANTN.primeReciprocal x-Real.log (Real.log x)) atTop (𝓝 B) ∧
      ∀ x : ℝ, Real.exp 300 ≤ x →
        |IEANTN.primeReciprocal x-Real.log (Real.log x)-B| ≤
          9*(9354674/1000000000:ℝ)*x^(-(1:ℝ)/8)/Real.log x := by
  have ray := (MainPiPsi300Read.pi_psi_300_from_actual_total_read read
    h hCHJ hrvm hsmall hlow hRH hQRH).1
  have input : ExposureTask.PrimeCountingInput := by
    intro t ht
    change IEANTN.Eπ t ≤ (9354674/1000000000:ℝ)*t^(-(1:ℝ)/8)
    simpa only [pow_zero,mul_one,show (7/8:ℝ)-1= -1/8 by norm_num] using ray t ht
  simpa only [reciprocal_alias,ExposureTask.C] using ExposureTask.final_consumer input

#print axioms pi_alias
#print axioms li_alias
#print axioms error_alias
#print axioms reciprocal_alias
#print axioms from_actual_total_read
end SynergyHeightC.ReciprocalRead300
