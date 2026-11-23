import BoxTailScalars
import BoxIntegrability
import StieltjesTrapezoid
import PurePiBounds
import IEANTN.Nodes.RHSmoothingInputs.v1.Conclusions
import IEANTN.Nodes.RHSmoothing.v1.Conclusions

namespace RHOcticPush.BoxTail
open Real Finset CLogMoment PsiSmoothing
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem source_moment_improved (hg : EulerHarmonicLower)
    (hs : StieltjesTrapezoidLower) (hm : MellinMomentIdentity)
    : J box 1 < 70871 / 100000 := by
  have interval128 := sample_interval (n := 128) (by norm_num) (by norm_num)
  have interval2 := sample_interval (n := 2) (by norm_num) (by norm_num)
  norm_num only [Nat.cast_ofNat] at interval128 interval2
  have num := exact_scalar_checks
  have hsum : (∑ n ∈ samples, (lower n : ℝ) / n) ≤
      ∑ n ∈ samples, Real.log n / n := by
    apply Finset.sum_le_sum
    intro n hn
    have hn' := Finset.mem_Icc.mp hn
    exact div_le_div_of_nonneg_right (sample_interval hn'.1 hn'.2).1 (by positivity)
  have sCast : (sLower : ℝ) = (∑ n ∈ samples, (lower n : ℝ) / n) -
      (upper 128 : ℝ) ^ 2 / 2 := by simp [sLower]
  have sn : (sLower : ℝ) ≤ stieltjesSeq 128 := by
    rw [sCast]
    unfold stieltjesSeq
    have lnonneg : 0 ≤ Real.log (128 : ℝ) := Real.log_nonneg (by norm_num)
    have usq : (Real.log (128 : ℝ)) ^ 2 ≤ (upper 128 : ℝ) ^ 2 := by
      nlinarith [interval128.2]
    change _ ≤ (∑ n ∈ samples, Real.log n / n) - Real.log 128 ^ 2 / 2
    linarith
  have st : (sLower : ℝ) - (upper 128 : ℝ) / 256 ≤ gamma1 := by
    unfold StieltjesTrapezoidLower at hs
    linarith [interval128.2]
  have qfull := q_lower_improved
  have g : (gammaLower : ℝ) ≤ Real.eulerMascheroniConstant := by
    unfold EulerHarmonicLower at hg
    have hgc : (gammaLower : ℝ) = (harmonic 1024 : ℝ) - 10 * (upper 2 : ℝ) -
        1 / 2048 := by simp [gammaLower]
    rw [hgc]
    linarith [interval2.2]
  have aBound : a ≤ (aUpper : ℝ) := by
    have ha : (aUpper : ℝ) = 1 - (gammaLower : ℝ) - (lower 2 : ℝ) := by simp [aUpper]
    rw [ha]
    unfold a
    linarith [interval2.1]
  have aneg : (aUpper : ℝ) < 0 := by exact_mod_cast num.2.1
  have lpos : (0 : ℝ) ≤ (lower 2 : ℝ) := by exact_mod_cast num.2.2
  have prod : a * Real.log 2 ≤ (aUpper : ℝ) * (lower 2 : ℝ) := by
    have x := mul_le_mul_of_nonpos_left interval2.1 (aBound.trans aneg.le)
    have y := mul_le_mul_of_nonneg_right aBound lpos
    linarith
  have asq : (aUpper : ℝ) ^ 2 ≤ a ^ 2 := by nlinarith
  have psq : Real.pi ^ 2 ≤ (31416 / 10000 : ℝ) ^ 2 := by
    have hpi := Real.pi_lt_d4
    have hp := Real.pi_pos
    nlinarith
  have hfc : (improvedUpper : ℝ) = -(sLower : ℝ) + (upper 128 : ℝ) / 256 -
      (qLower : ℝ) + (aUpper : ℝ) * (lower 2 : ℝ) - (aUpper : ℝ) ^ 2 / 2 +
      1 / 2 + (31416 / 10000 : ℝ) ^ 2 / 24 - (tailCorrection : ℝ) := by
    simp [improvedUpper, finalUpper]
  have hbound : J box 1 ≤ (improvedUpper : ℝ) := by
    unfold MellinMomentIdentity at hm
    rw [hm, hfc]
    linarith
  have hf : (improvedUpper : ℝ) < ((70871 / 100000 : ℚ) : ℝ) :=
    Rat.cast_lt.mpr scalar_improved.1
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hf
  exact hbound.trans_lt hf


/-- The same two exact Mellin identities supply the strictly improved cap. -/
theorem source_moment_improved_closed
    (hm : BoxMellinInputs.v1.second_moment_identity) : J box 1 < 70871/100000 :=
  source_moment_improved EulerLower.harmonic1024_lower
    RHLimit.Stieltjes.stieltjes_trapezoid.2 hm.2

noncomputable def improvedBound (L : ℝ) : ℝ :=
  envelope (Real.log 2) (70871/100000) L

/-- Exact strict gain in the complete psi-envelope, at every real logarithm. -/
theorem envelope_gain (L : ℝ) :
    IEANTN.RHSmoothing.fastBound L - improvedBound L = (1/25000)/Real.pi := by
  unfold IEANTN.RHSmoothing.fastBound IEANTN.RHSmoothing.envelope
    IEANTN.RHSmoothing.v improvedBound envelope v
  ring

/-- Actual whole-real-ray psi, reusing exactly the prior C log input domain. -/
theorem actual_psi_improved (rh : RiemannHypothesis)
    (hef : RHSmoothingInputs.v1.box_explicit_formula)
    (hz : RHSmoothingInputs.v1.box_zero_estimate)
    (hfirst : BoxMellinInputs.v1.first_moment)
    (hsecond : BoxMellinInputs.v1.second_moment_identity) :
    ∀ x : ℝ, Real.exp 35 ≤ x → |Chebyshev.psi x-x| ≤
      Real.sqrt x * improvedBound (Real.log x) := by
  intro x hx
  have hx0 : 0<x := (Real.exp_pos 35).trans_le hx
  have hL : 35 ≤ Real.log x := by
    have h := Real.log_le_log (Real.exp_pos 35) hx
    simpa only [Real.log_exp] using h
  have hh := psi_from_smoothing box box_continuous box_nonneg box_mass
    rh hef hz RHContinuation.PsiElementary.box_main RHContinuation.PsiElementary.box_trivial
    (le_of_eq hfirst.2) (source_moment_improved_closed hsecond).le (Real.log x) hL
  simpa only [Real.exp_log hx0, improvedBound] using hh

/-- The stronger output is genuinely accepted by the unchanged canonical node. -/
theorem canonical_box_psi (rh : RiemannHypothesis)
    (hef : RHSmoothingInputs.v1.box_explicit_formula)
    (hz : RHSmoothingInputs.v1.box_zero_estimate)
    (hfirst : BoxMellinInputs.v1.first_moment)
    (hsecond : BoxMellinInputs.v1.second_moment_identity) :
    RHSmoothing.v1.box_psi := by
  intro x hx
  have h := actual_psi_improved rh hef hz hfirst hsecond x hx
  have he := envelope_gain (Real.log x)
  have hpos : (0:ℝ)<(1/25000)/Real.pi := by positivity
  apply h.trans
  exact mul_le_mul_of_nonneg_left (by linarith) (Real.sqrt_nonneg _)

/-- Existing generic psi-to-ordinary-pi transport consumes the improved function. -/
theorem actual_pi_Li_improved (rh : SharedRH.hypothesis)
    (hef : RHSmoothingInputs.v1.box_explicit_formula)
    (hz : RHSmoothingInputs.v1.box_zero_estimate)
    (hfirst : BoxMellinInputs.v1.first_moment)
    (hsecond : BoxMellinInputs.v1.second_moment_identity)
    (hGM : RHContinuation.Ramanujan.GM_Q_Theorem1_1)
    (hP : Buthe.v1.theorem_2_psi)
    (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    {L : ℝ} (hL : 35 ≤ L) :
    |IEANTN.primeCounting (Real.exp L)-IEANTN.Li (Real.exp L)| ≤
      RHLimit.PurePi.envelope improvedBound L + 2 := by
  apply RHLimit.PurePi.actual_pi_Li_elementary rh hGM hP hJ improvedBound
    (by linarith)
  have h := actual_psi_improved rh hef hz hfirst hsecond (Real.exp L)
    (Real.exp_le_exp.mpr hL)
  simpa only [Real.log_exp] using h

/-- No weaker old component is used to manufacture the pi comparison. -/
theorem pi_envelope_gain (L : ℝ) :
    RHLimit.PurePi.envelope IEANTN.RHSmoothing.fastBound L -
      RHLimit.PurePi.envelope improvedBound L =
      Real.exp (L/2)/L * ((1/25000)/Real.pi) := by
  have h := envelope_gain L
  calc
    _ = Real.exp (L/2)/L *
        (IEANTN.RHSmoothing.fastBound L - improvedBound L) := by
      unfold RHLimit.PurePi.envelope
      ring
    _ = _ := by rw [h]

#print axioms source_moment_improved_closed
#print axioms actual_psi_improved
#print axioms canonical_box_psi
#print axioms actual_pi_Li_improved
#print axioms pi_envelope_gain
end RHOcticPush.BoxTail
