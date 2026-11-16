/- A full-function prime-rich consumer of the same actual source-main total read.
Original onset and count retained; width is uniformly below0.017 and decreases. -/
import SynergyHeightC.MainRationalProgram
import SynergyAnalytic.RationalPrimeRichFunction
namespace SynergyHeightC.MainPrimeRichFunctionProgram
open ScopedC ScopedC.Machine ScopedNumerical SynergyBasis ScopedIO
open SynergyAnalytic SynergyAnalytic.HeightPoint SynergyHeightC.MainWeightModel
open Real IEANTN WinnerOriginalScalars WinnerNewHeightSource WinnerDirectKernel
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 100000

theorem main_observed_prime_rich_function (platform : WorldIO.Platform) (initial : Stream)
    (h : PrimaryInputs (3681/10000) (3599/10000))
    (hCHJ : OriginalCHJSource) (hrvm : ZeroCount.v1.rvm_error_bound)
    (hsmall : ZeroCount.v1.rvm_error_small)
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    (hRH : RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH : ZetaZeroFreeHalfPlane (7/8)) {x : ℝ} (hx : Real.exp 330 ≤ x) :
    ∃ (trace : Nat → Stream) (final : WorldIO.World),
      trace 0=initial ∧
      WorldSource.SourceCall SynergyC.Header.layout Bundle.code platform CompleteIOModel.policy
        3 "main" [] ⟨Initialization.initializeBoundGlobals.getD Machine.empty,initial⟩
        (WorldIO.signed32 0) ⟨FullMainPrefix.cache,final.stream⟩ ∧
      final.stream.accepted=(trace 768).accepted++MainObservedOutput.bytes ∧
      final.stream.delivered=final.stream.accepted.length ∧
      rationalRichWidth (8433850764/1000000000000) (Real.log x)<17/1000 ∧
      (57/500000:ℝ)*x^((7:ℝ)/8)/Real.log x ≤
        primeCounting (x+rationalRichWidth (8433850764/1000000000000) (Real.log x)*
          x^((7:ℝ)/8))-primeCounting x := by
  obtain ⟨trace,final,out,start,source,read,bytes,delivered,sum,bound,oldMathematical⟩ :=
    MainCompleteModel.complete_source_main_and_pnt platform initial h hCHJ hrvm hsmall hlow hRH hQRH
  have profile : ∀ z ≥ Real.exp 330,
      Eπ z ≤ rationalHeightCoefficient (8433850764/1000000000000) (Real.log z)*z^(-(1:ℝ)/8) :=
    fun z hz=>MainRationalRead.pi_rational_point_from_actual_total_read read
      SourcePointSlopesV1.All.bounds h hCHJ hrvm hsmall hlow hRH hQRH hz
  have mathematical := prime_rich_rational_function (by norm_num) rational_checkpoint_330 profile hx
  have logX : 330 ≤ Real.log x := by
    have compared := Real.log_le_log (Real.exp_pos (330:ℝ)) hx
    simpa only [Real.log_exp] using compared
  have width := rationalRichWidth_smaller (by norm_num) rational_checkpoint_330 logX
  have observed : out=MainObservedOutput.total :=
    (MainFinalTotal.actual_read_identity read).trans MainObservedOutput.total_exact
  rw [observed] at bytes
  have actualBytes : final.stream.accepted=(trace 768).accepted++MainObservedOutput.bytes := by
    rw [MainObservedOutput.bytes_exact,←List.append_assoc]
    exact bytes
  exact ⟨trace,final,start,source,actualBytes,delivered,width,mathematical⟩

#print axioms main_observed_prime_rich_function
end SynergyHeightC.MainPrimeRichFunctionProgram
