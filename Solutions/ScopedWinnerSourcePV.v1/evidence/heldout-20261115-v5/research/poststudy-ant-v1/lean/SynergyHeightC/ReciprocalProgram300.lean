/- Whole unchanged initialized C main and same observed total feed the new
actual-prime reciprocal limit and full-ray error, poststudy integration only. -/
import SynergyHeightC.ReciprocalRead300
import SynergyHeightC.MainObservedProgram
namespace SynergyHeightC.ReciprocalProgram300
open ScopedC ScopedC.Machine ScopedNumerical SynergyBasis ScopedIO
open Real IEANTN WinnerOriginalScalars WinnerNewHeightSource WinnerDirectKernel
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 100000
open Filter
open scoped Topology

theorem main_observed_prime_reciprocal (platform : WorldIO.Platform) (initial : Stream)
    (h : PrimaryInputs (3681/10000) (3599/10000))
    (hCHJ : OriginalCHJSource) (hrvm : ZeroCount.v1.rvm_error_bound)
    (hsmall : ZeroCount.v1.rvm_error_small)
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    (hRH : RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH : ZetaZeroFreeHalfPlane (7/8)) :
    ∃ (trace : Nat → Stream) (final : WorldIO.World) (B : ℝ),
      trace 0=initial ∧
      WorldSource.SourceCall SynergyC.Header.layout Bundle.code platform CompleteIOModel.policy
        3 "main" [] ⟨Initialization.initializeBoundGlobals.getD Machine.empty,initial⟩
        (WorldIO.signed32 0) ⟨FullMainPrefix.cache,final.stream⟩ ∧
      final.stream.accepted=(trace 768).accepted++MainObservedOutput.bytes ∧
      final.stream.delivered=final.stream.accepted.length ∧
      Tendsto (fun x : ℝ => IEANTN.primeReciprocal x-Real.log (Real.log x)) atTop (𝓝 B) ∧
      ∀ x : ℝ, Real.exp 300 ≤ x →
        |IEANTN.primeReciprocal x-Real.log (Real.log x)-B| ≤
          9*(9354674/1000000000:ℝ)*x^(-(1:ℝ)/8)/Real.log x := by
  obtain ⟨trace,final,out,start,source,read,bytes,delivered,sum,bound,oldMathematical⟩ :=
    MainCompleteModel.complete_source_main_and_pnt platform initial h hCHJ hrvm hsmall hlow hRH hQRH
  obtain ⟨B,converges,estimate⟩ := ReciprocalRead300.from_actual_total_read read
    h hCHJ hrvm hsmall hlow hRH hQRH
  have observed : out=MainObservedOutput.total :=
    (MainFinalTotal.actual_read_identity read).trans MainObservedOutput.total_exact
  rw [observed] at bytes
  have actualBytes : final.stream.accepted=(trace 768).accepted++MainObservedOutput.bytes := by
    rw [MainObservedOutput.bytes_exact,←List.append_assoc]
    exact bytes
  exact ⟨trace,final,B,start,source,actualBytes,delivered,converges,estimate⟩

#print axioms main_observed_prime_reciprocal
end SynergyHeightC.ReciprocalProgram300
