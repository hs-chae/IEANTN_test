/- Actual initialized C main and observed footer supporting the arithmetic
psi-to-theta consumer; no new analytic input or program algorithm. -/
import SynergyHeightC.ThetaRead300
import SynergyHeightC.MainObservedProgram
namespace SynergyHeightC.ThetaProgram300
open ScopedC ScopedC.Machine ScopedNumerical SynergyBasis ScopedIO
open Real IEANTN WinnerOriginalScalars WinnerNewHeightSource WinnerDirectKernel
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 100000

theorem main_observed_theta (platform : WorldIO.Platform) (initial : Stream)
    (h : PrimaryInputs (3681/10000) (3599/10000))
    (hCHJ : OriginalCHJSource) (hrvm : ZeroCount.v1.rvm_error_bound)
    (hsmall : ZeroCount.v1.rvm_error_small)
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    (hRH : RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH : ZetaZeroFreeHalfPlane (7/8)) {x : ℝ} (hx : Real.exp 300 ≤ x) :
    ∃ (trace : Nat → Stream) (final : WorldIO.World),
      trace 0=initial ∧
      WorldSource.SourceCall SynergyC.Header.layout Bundle.code platform CompleteIOModel.policy
        3 "main" [] ⟨Initialization.initializeBoundGlobals.getD Machine.empty,initial⟩
        (WorldIO.signed32 0) ⟨FullMainPrefix.cache,final.stream⟩ ∧
      final.stream.accepted=(trace 768).accepted++MainObservedOutput.bytes ∧
      final.stream.delivered=final.stream.accepted.length ∧
      Eθ x ≤ (9354674/1000000000:ℝ)*x^(-(1:ℝ)/8)+(2*Real.sqrt x*Real.log x)/x ∧
      Eθ x ≤ ((9354674/1000000000:ℝ)+16/Real.exp 75)*x^(-(1:ℝ)/8) ∧
      Eθ x ≤ ((9354674/1000000000:ℝ)+1/1000000000)*x^(-(1:ℝ)/8) := by
  obtain ⟨trace,final,out,start,source,read,bytes,delivered,sum,bound,oldMathematical⟩ :=
    MainCompleteModel.complete_source_main_and_pnt platform initial h hCHJ hrvm hsmall hlow hRH hQRH
  have bounds := ThetaRead300.from_actual_total_read read
    h hCHJ hrvm hsmall hlow hRH hQRH hx
  have observed : out=MainObservedOutput.total :=
    (MainFinalTotal.actual_read_identity read).trans MainObservedOutput.total_exact
  rw [observed] at bytes
  have actualBytes : final.stream.accepted=(trace 768).accepted++MainObservedOutput.bytes := by
    rw [MainObservedOutput.bytes_exact,←List.append_assoc]
    exact bytes
  exact ⟨trace,final,start,source,actualBytes,delivered,bounds.1,bounds.2.1,bounds.2.2⟩

#print axioms main_observed_theta
end SynergyHeightC.ThetaProgram300
