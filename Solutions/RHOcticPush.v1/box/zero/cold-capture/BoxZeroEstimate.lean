import BoxPacketBound
import BoxUnshiftedBound
import BoxZeroScalarExtra
import BoxZeroInflation
import OcticBPTSourceEndpoint
import IEANTN.Nodes.RHSmoothingInputs.v1.Conclusions

/-! The exact original complete Box zero estimate. Actual source packets,
full-family summability, every ordinate/multiplicity, full integrals and both
shifts are consumed. Only genuine general Nicolas/BPT inputs remain explicit. -/
namespace RHOcticPush.BoxZero
open Real Set MeasureTheory Filter IEANTN.RHSmoothing
open RHLimit.BPTZeroCount RHOcticPush.BPTInfinite
set_option maxHeartbeats 0

/-- Stronger than the original predicate: actual full packet summability is also
provided, and the argument works for every real shift s<=1. -/
theorem actual_zero_average_bound (hN : NicolasContinuation.SourceNicolas119)
    (hB : PublishedBound) (rh : RiemannHypothesis) {s L : ℝ}
    (hL : 35≤L) (hs : s≤1) :
    Summable (IEANTN.RHSmoothing.zeroPacket box s L) ∧
    ‖zeroAverage box s L‖ ≤ Real.sqrt (Real.exp L) *
      ((v L^2+2*J box 0*v L+2*J box 1)/(2*Real.pi)+131/1000) := by
  have hd := delta_small hL
  have hsmall : 12*delta L≤1 := by linarith [hd.2]
  have hp (z : PsiSmoothing.Zero) :
      ‖IEANTN.RHSmoothing.zeroPacket box s L z‖ ≤
        (Real.exp (L/2)*Real.exp (delta L))*transportMajorant (delta L) z.val.im*
          (IEANTN.zetaOrder z.val : ℝ) := by
    by_cases hz : |z.val.im|≤12
    · have ho := RHOcticPush.ZeroPairing.order_zero_low rh hN hB z hz
      simp [IEANTN.RHSmoothing.zeroPacket,ho]
    · exact actual_packet_majorant rh hd.1 hs z (lt_of_not_ge hz)
  have ht := complete_transport_bound rh hN hB hd.1
    (X := Real.exp (L/2)*Real.exp (delta L)) (by positivity) hp
  have hu := unshifted_positive_bound hB hd.1 hsmall
  have hi := exp_main_inflation hd.1.le (by linarith [hd.2] : delta L≤1/2)
    (mainMoment_actual_bound hL)
  have hr := uniform_zero_residual_with_lowHole hL
  refine ⟨ht.1,?_⟩
  change ‖∑' z : PsiSmoothing.Zero,IEANTN.RHSmoothing.zeroPacket box s L z‖ ≤ _
  calc
    _ ≤ (Real.exp (L/2)*Real.exp (delta L))*
        (2*(∑' z : PositiveZero 12,|kernel (delta L) z.val.im| *
          (IEANTN.zetaOrder z.val : ℝ))+shiftAllowance (delta L)) := ht.2
    _ ≤ (Real.exp (L/2)*Real.exp (delta L))*
        (mainMoment (delta L)+endpointAllowance+derivativeAllowance (delta L)+
          4*(delta L)^2+shiftAllowance (delta L)) := by
      exact mul_le_mul_of_nonneg_left (add_le_add hu le_rfl) (by positivity)
    _ = Real.exp (L/2)*(Real.exp (delta L)*mainMoment (delta L)+
        Real.exp (delta L)*(endpointAllowance+derivativeAllowance (delta L)+
          shiftAllowance (delta L)+4*(delta L)^2)) := by ring
    _ ≤ Real.exp (L/2)*(mainMoment (delta L)+2*delta L*L^2+
        Real.exp (delta L)*(endpointAllowance+derivativeAllowance (delta L)+
          shiftAllowance (delta L)+4*(delta L)^2)) := by
      exact mul_le_mul_of_nonneg_left (add_le_add hi le_rfl) (Real.exp_pos _).le
    _ ≤ Real.exp (L/2)*(mainMoment (delta L)+131/1000) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      linarith
    _ = _ := by rw [← sqrt_exp_half,actual_mainMoment (by linarith : 0<L)]

/-- The unchanged canonical Box zero-estimate predicate, with all newly created
analytic obligations discharged and no moment or pointwise-packet binder. -/
theorem box_zero_estimate (hN : NicolasContinuation.SourceNicolas119)
    (hB : PublishedBound) : RHSmoothingInputs.v1.box_zero_estimate := by
  intro rh L hL s hs
  apply (actual_zero_average_bound hN hB rh hL ?_).2
  rcases hs with rfl|rfl <;> norm_num

/-- Source-correct endpoint interface; the published off-ordinate bound is
transferred to every actual closed height by the already proved right limit. -/
theorem box_zero_estimate_offOrdinate (hN : NicolasContinuation.SourceNicolas119)
    (hB : RHOcticPush.BPTSourceEndpoint.SourceBPTOffOrdinate) :
    RHSmoothingInputs.v1.box_zero_estimate :=
  box_zero_estimate hN (RHOcticPush.BPTSourceEndpoint.publishedBound_of_offOrdinate hB)

#print axioms actual_zero_average_bound
#print axioms box_zero_estimate
#print axioms box_zero_estimate_offOrdinate
#check @box_zero_estimate_offOrdinate
end RHOcticPush.BoxZero
