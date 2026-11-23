import LimitPiSolution
import LimitKernelSolution
import LimitMellinSolution
import LimitRamSolution
import OldRamFullSolution

/-! Final source-conditional mathematical consumers. Existing canonical results
are consumed by their actual proved Solutions; no target predicate is silently
introduced as a new analytic assumption. -/
namespace RHLimit.Network
open Real IEANTN
set_option maxHeartbeats 0

theorem octic_forward_evolution (rh : RH.v1.hypothesis)
    (hef : PrimeKernelInputs.v2.octic_215_explicit_formula)
    (hz : PrimeKernelInputs.v2.octic_215_zero_estimate) :
    PrimeInterval.v2.count_215 ∧ PrimeQuantile.v1.octic_block ∧
      PrimeQuantile.v1.successive_cubes := by
  have hi := PrimeKernelInputs.v1.challenge_octic_215 hef hz
  have hc := RHContinuation.Network.count_215 rh hi
  exact ⟨hc,RHContinuation.Network.octic_block hc,
    RHContinuation.Network.successive_cubes hc⟩

theorem box_forward_evolution (rh : RH.v1.hypothesis)
    (hef : RHSmoothingInputs.v1.box_explicit_formula)
    (hz : RHSmoothingInputs.v1.box_zero_estimate)
    (hfirst : BoxMellinInputs.v1.first_moment)
    (hsecond : BoxMellinInputs.v1.second_moment_identity)
    (hg : RHPrimeCounting.v1.gm_source) (hp : Buthe.v1.theorem_2_psi)
    (hj : Buthe.v1.theorem_2_li_minus_riemann_pi) :
    RHSmoothing.v1.box_psi ∧ Lcm.v4.box_growth ∧ RHPrimeCounting.v2.box_Epi := by
  have hb := RHLimit.BoxMomentReduced.box_psi rh hef hz hfirst hsecond
  exact ⟨hb,RHContinuation.Network.box_lcm hb,
    RHPrimeCounting.v2.challenge_box_Epi rh hg hp hj hb⟩

/-- Entire previous strongest profile is supplied by its actual completed proof,
not assumed as an additional target predicate. All nine source inputs are visible. -/
theorem ramanujan_full_source_evolution (rh : RH.v1.hypothesis)
    (hg : RHPrimeCounting.v1.gm_source) (hp : Buthe.v1.theorem_2_psi)
    (hj : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (h1 : Buthe.v1.table_1_interval_bounds) (h2 : Buthe.v1.table_2_interval_bounds)
    (hl : Buthe.v1.theorem_2_li_minus_pi) (hu : Buthe.v1.theorem_2_li_gt_pi)
    (hs : Buthe2016.v1.theorem_2_li_minus_pi) :
    RamanujanGap.v4.full_profile ∧ RamanujanGap.v4.ramanujan := by
  have hnew := RamanujanGap.v4.challenge_margin_620b rh hg hp hj h1 h2 hl hu hs
  have hold := RamanujanGap.v3.challenge_full_profile rh h2 hj hl hu hs
  exact ⟨RamanujanGap.v4.challenge_full_profile hnew hold,
    RamanujanGap.v4.challenge_ramanujan hnew⟩

#print axioms octic_forward_evolution
#print axioms box_forward_evolution
#print axioms ramanujan_full_source_evolution
end RHLimit.Network
