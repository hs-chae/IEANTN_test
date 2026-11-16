/- The unchanged analytic hypotheses with actual C point outputs and the exact
C-expression sum. Full main/stream/run association remains a separate proof. -/
import SourceMainWeightsV1.All
import SourceMainFramesV1.All
import SynergyHeightC.MainWeightPNT
namespace SourceMainWeightsV1.PNT
open ScopedNumerical SynergyBasis SynergyAnalytic SynergyAnalytic.HeightPoint
open SynergyHeightC.MainWeightModel
open Real IEANTN WinnerOriginalScalars WinnerNewHeightSource WinnerDirectKernel
set_option autoImplicit false
set_option maxHeartbeats 200000

theorem actual_word_bound : realWord SourceMainWeightsV1.All.total.hi ≤
    8433850764/1000000000000 := by
  have hh : (SourceMainWeightsV1.All.total.hi:ℝ)*1000000000000 ≤
      8433850764*(ProofBox.scale 128:ℝ) := by
    exact_mod_cast SourceMainWeightsV1.All.upper_word_bound
  apply (div_le_iff₀ (RealBox.scale_real_pos 128)).mpr
  linarith

theorem source_pi_actual_weights
    (h : PrimaryInputs (3681/10000) (3599/10000))
    (hCHJ : OriginalCHJSource) (hrvm : ZeroCount.v1.rvm_error_bound)
    (hsmall : ZeroCount.v1.rvm_error_small)
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    (hRH : RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH : ZetaZeroFreeHalfPlane (7/8)) :
    HasPowerLogBound Eπ (8441646/1000000000) 0 (7/8) (Real.exp 330) :=
  pi_008441646_from_actual_weights (SourceMainFramesV1.All.outputs ⟨0,0⟩)
    SourceMainWeightsV1.All.all_domains SourceMainWeightsV1.All.exact_total
    actual_word_bound h hCHJ hrvm hsmall hlow hRH hQRH

end SourceMainWeightsV1.PNT
#print axioms SourceMainWeightsV1.PNT.actual_word_bound
#print axioms SourceMainWeightsV1.PNT.source_pi_actual_weights
