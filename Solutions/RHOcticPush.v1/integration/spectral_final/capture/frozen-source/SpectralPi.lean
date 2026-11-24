import SpectralFinal
import EvolvedPi
import BoxExplicitFormula
import BoxZeroEstimate
import BoxFirstMoment
import BoxSecondMoment
import BoxImproved

/-! The actual signed-zero improvement reaches ordinary prime counting and
interval populations. Actual prime-power and offset-Li corrections are paid.
The complete Box instance constructs every old analytic provider internally. -/
namespace RHOcticPush.Spectral076
open Real IEANTN Set
open RHContinuation.Ramanujan RHLimit.PrimePower RHOcticPush.BoxPerron
set_option maxHeartbeats 0

noncomputable def piEnvelope (f : ℝ → ℝ) (L : ℝ) : ℝ :=
  Real.exp (L/2)/L*f L+profile L+elementaryRemainder L+2

theorem actual_J_profile (rh : RiemannHypothesis)
    (hN : NicolasContinuation.SourceNicolas119) (hI : SourceIntegratedPsi)
    (f : ℝ → ℝ) {L : ℝ} (hL : 24 ≤ L)
    (hpsi : |Chebyshev.psi (Real.exp L)-Real.exp L| ≤ Real.sqrt (Real.exp L)*f L) :
    |riemannPrimeCounting (Real.exp L)-IEANTN.li (Real.exp L)| ≤
      Real.exp (L/2)/L*f L+profile L := by
  have h0 : 0 < L := by linarith
  have hd := actual_compensation_profile rh hN hI (Real.exp_le_exp.mpr hL)
  rw [Real.log_exp] at hd
  have hp : |(Chebyshev.psi (Real.exp L)-Real.exp L)/L| ≤
      Real.exp (L/2)/L*f L := by
    rw [abs_div,abs_of_pos h0]
    have h := div_le_div_of_nonneg_right hpsi h0.le
    rw [←Real.exp_half] at h
    convert! h using 1 <;> ring
  unfold RHOcticPush.GM.error at hd
  have h := abs_add_le
    (riemannPrimeCounting (Real.exp L)-IEANTN.li (Real.exp L)-
      (Chebyshev.psi (Real.exp L)-Real.exp L)/L)
    ((Chebyshev.psi (Real.exp L)-Real.exp L)/L)
  simp only [Real.log_exp,sub_add_cancel] at hd h
  linarith

/-- Explicit ordinary-pi consumer on all real logarithms, with no GM/Büthe
source bound assumed to prove the new signed transfer. -/
theorem actual_pi_Li (rh : RiemannHypothesis)
    (hN : NicolasContinuation.SourceNicolas119) (hI : SourceIntegratedPsi)
    (f : ℝ → ℝ) {L : ℝ} (hL : 24 ≤ L)
    (hpsi : |Chebyshev.psi (Real.exp L)-Real.exp L| ≤ Real.sqrt (Real.exp L)*f L) :
    |primeCounting (Real.exp L)-IEANTN.Li (Real.exp L)| ≤ piEnvelope f L := by
  have hj := actual_J_profile rh hN hI f hL hpsi
  have hq := actual_remainder_elementary (by linarith : (2:ℝ)≤L)
  have hq0 := actual_prime_power_nonnegative (Real.exp_pos L)
  have htri := abs_sub_le (riemannPrimeCounting (Real.exp L)-IEANTN.li (Real.exp L))
    (0:ℝ) (riemannPrimeCounting (Real.exp L)-primeCounting (Real.exp L))
  simp only [sub_zero,zero_sub,abs_neg,abs_of_nonneg hq0] at htri
  have hpi : |primeCounting (Real.exp L)-IEANTN.li (Real.exp L)| ≤
      Real.exp (L/2)/L*f L+profile L+elementaryRemainder L := by
    have he : primeCounting (Real.exp L)-IEANTN.li (Real.exp L) =
        (riemannPrimeCounting (Real.exp L)-IEANTN.li (Real.exp L))-
          (riemannPrimeCounting (Real.exp L)-primeCounting (Real.exp L)) := by ring
    rw [he]
    linarith
  have hoff := actual_li_Li_offset (Real.one_lt_exp_iff.mpr (by linarith : (0:ℝ)<L))
  have h2 := RHLimit.PurePi.li_two_bounds
  have he : primeCounting (Real.exp L)-IEANTN.Li (Real.exp L) =
      (primeCounting (Real.exp L)-IEANTN.li (Real.exp L))+IEANTN.li 2 := by linarith
  rw [he]
  have htri := abs_add_le (primeCounting (Real.exp L)-IEANTN.li (Real.exp L)) (IEANTN.li 2)
  rw [abs_of_nonneg h2.1] at htri
  unfold piEnvelope
  linarith

/-- Complete source-to-ordinary-pi instance: the former four Box obligations
are all constructed, and the new actual signed compensation is consumed. -/
theorem actual_box_pi (rh : RiemannHypothesis)
    (hN : NicolasContinuation.SourceNicolas119) (hI : SourceIntegratedPsi)
    (hB : RHOcticPush.BPTSourceEndpoint.SourceBPTOffOrdinate)
    {L : ℝ} (hL : 35 ≤ L) :
    |primeCounting (Real.exp L)-IEANTN.Li (Real.exp L)| ≤
      piEnvelope RHOcticPush.BoxTail.improvedBound L := by
  have he := RHOcticPush.BoxPerron.box_explicit_formula hI
  have hz := RHOcticPush.BoxZero.box_zero_estimate_offOrdinate hN hB
  have hp := RHOcticPush.BoxTail.actual_psi_improved rh he hz
    RHOcticPush.BoxGamma.first_moment RHOcticPush.BoxGamma.second_moment_identity
    (Real.exp L) (Real.exp_le_exp.mpr hL)
  rw [Real.log_exp] at hp
  exact actual_pi_Li rh hN hI RHOcticPush.BoxTail.improvedBound (by linarith) hp

/-- Complete actual interval-population consumer; no ordering assumption is
needed for the algebraic difference, and both endpoint errors are explicit. -/
theorem actual_box_interval (rh : RiemannHypothesis)
    (hN : NicolasContinuation.SourceNicolas119) (hI : SourceIntegratedPsi)
    (hB : RHOcticPush.BPTSourceEndpoint.SourceBPTOffOrdinate)
    {A B : ℝ} (hA : 35 ≤ A) (hBB : 35 ≤ B) :
    IEANTN.Li (Real.exp B)-IEANTN.Li (Real.exp A)-
      piEnvelope RHOcticPush.BoxTail.improvedBound A-
      piEnvelope RHOcticPush.BoxTail.improvedBound B ≤
      primeCounting (Real.exp B)-primeCounting (Real.exp A) := by
  have ha := (abs_le.mp (actual_box_pi rh hN hI hB hA)).2
  have hb := (abs_le.mp (actual_box_pi rh hN hI hB hBB)).1
  linarith

#print axioms actual_J_profile
#print axioms actual_pi_Li
#print axioms actual_box_pi
#print axioms actual_box_interval
end RHOcticPush.Spectral076
