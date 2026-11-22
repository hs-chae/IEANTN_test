import PurePiRay
import BoxMomentReduced
namespace RHLimit.PurePi
open Real IEANTN RHContinuation.Ramanujan
set_option maxHeartbeats 0

/-- Actual C source→verified execution→moment cap→actual box psi→ordinary pi.
The four analytic inputs and named GM/Büthe source inputs remain explicit. -/
theorem source_box_Epi
    (rh : SharedRH.hypothesis)
    (hef : RHSmoothingInputs.v1.box_explicit_formula)
    (hz : RHSmoothingInputs.v1.box_zero_estimate)
    (hfirst : BoxMellinInputs.v1.first_moment)
    (hsecond : BoxMellinInputs.v1.second_moment_identity)
    (hGM : GM_Q_Theorem1_1) (hP : Buthe.v1.theorem_2_psi)
    (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    {L : ℝ} (hL : 35 ≤ L) :
    Eπ (exp L) ≤ normalized RHSmoothing.fastBound L*exp (-L/2) :=
  box_Epi_from_moments rh hef hz
    (RHLimit.BoxMomentReduced.box_moments hfirst hsecond) hGM hP hJ hL

theorem source_box_Epi_at_100
    (rh : SharedRH.hypothesis)
    (hef : RHSmoothingInputs.v1.box_explicit_formula)
    (hz : RHSmoothingInputs.v1.box_zero_estimate)
    (hfirst : BoxMellinInputs.v1.first_moment)
    (hsecond : BoxMellinInputs.v1.second_moment_identity)
    (hGM : GM_Q_Theorem1_1) (hP : Buthe.v1.theorem_2_psi)
    (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi) :
    Eπ (exp 100) < (357041/1000:ℝ)*exp (-50) := by
  have h := source_box_Epi rh hef hz hfirst hsecond hGM hP hJ (by norm_num : (35:ℝ)≤100)
  have h2 := mul_lt_mul_of_pos_right box_at_100 (exp_pos (-50:ℝ))
  norm_num at h
  exact h.trans_lt h2

#print axioms source_box_Epi
#print axioms source_box_Epi_at_100
end RHLimit.PurePi
