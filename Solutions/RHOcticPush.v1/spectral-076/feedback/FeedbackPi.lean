import FeedbackPrimePowers

/-! The actual prime-square feedback reaches ordinary prime counting with the
same four inputs. The complete old35-ray is retained; above70 the whole raw
lower-scale J function is used through a minimum, before any simplification. -/
namespace RHOcticPush.PrimeSquareFeedback
open Real IEANTN RHContinuation.Ramanujan RHLimit.PrimePower RHOcticPush.BoxPerron
set_option maxHeartbeats 0

noncomputable def envelope (f : ℝ → ℝ) (L : ℝ) : ℝ :=
  Real.exp (L/2)/L*f L+Spectral076.profile L+effectiveRemainder L+2
noncomputable def rawEnvelope (f : ℝ → ℝ) (L : ℝ) : ℝ :=
  Real.exp (L/2)/L*f L+Spectral076.profile L+rawRemainder L+2
noncomputable def simplifiedEnvelope (f : ℝ → ℝ) (L : ℝ) : ℝ :=
  Real.exp (L/2)/L*f L+Spectral076.profile L+remainder L+2

lemma envelope_le_old (f : ℝ → ℝ) (L : ℝ) :
    envelope f L ≤ Spectral076.piEnvelope f L := by
  have h := effective_le_old L
  unfold envelope Spectral076.piEnvelope
  linarith

lemma envelope_eq_old {L : ℝ} (hL : L < 70) (f : ℝ → ℝ) :
    envelope f L = Spectral076.piEnvelope f L := by
  unfold envelope Spectral076.piEnvelope effectiveRemainder
  rw [if_neg (by linarith : ¬70≤L)]

lemma envelope_le_raw {L : ℝ} (hL : 70 ≤ L) (f : ℝ → ℝ) :
    envelope f L ≤ rawEnvelope f L := by
  have h := effective_le_raw hL
  unfold envelope rawEnvelope
  linarith

lemma envelope_eq_min {L : ℝ} (hL : 70 ≤ L) (f : ℝ → ℝ) :
    envelope f L = min (Spectral076.piEnvelope f L) (rawEnvelope f L) := by
  unfold envelope Spectral076.piEnvelope rawEnvelope effectiveRemainder
  rw [if_pos hL]
  by_cases h : elementaryRemainder L ≤ rawRemainder L
  · rw [min_eq_left h,min_eq_left (by linarith)]
  · rw [min_eq_right (by linarith : rawRemainder L ≤ elementaryRemainder L),
      min_eq_right (by linarith)]

lemma envelope_lt_simplified {L : ℝ} (hL : 100 ≤ L) (f : ℝ → ℝ) :
    envelope f L < simplifiedEnvelope f L := by
  have h := effective_lt_simplified hL
  unfold envelope simplifiedEnvelope
  linarith

lemma simplified_envelope_gain (f : ℝ → ℝ) (L : ℝ) :
    Spectral076.piEnvelope f L-simplifiedEnvelope f L =
      (2*Real.log 4-(11/10 : ℝ))*Real.exp (L/2)/L := by
  have h := remainder_gain L
  unfold Spectral076.piEnvelope simplifiedEnvelope
  linarith

/-- A strict improvement of the entire function, with the same inputs/onset,
not just of its leading coefficient. All other corrections cancel exactly. -/
theorem envelope_strict_gain {L : ℝ} (hL : 100 ≤ L) (f : ℝ → ℝ) :
    (167/100 : ℝ)*Real.exp (L/2)/L < Spectral076.piEnvelope f L-envelope f L := by
  have h := effective_strict_gain hL
  unfold Spectral076.piEnvelope envelope
  linarith

/-- Generic full ordinary-pi transfer using the actual effective Q theorem. -/
theorem actual_pi_feedback (rh : RiemannHypothesis)
    (hN : NicolasContinuation.SourceNicolas119) (hI : SourceIntegratedPsi)
    (hB : RHOcticPush.BPTSourceEndpoint.SourceBPTOffOrdinate)
    (f : ℝ → ℝ) {L : ℝ} (hL : 35 ≤ L)
    (hpsi : |Chebyshev.psi (Real.exp L)-Real.exp L| ≤ Real.sqrt (Real.exp L)*f L) :
    |primeCounting (Real.exp L)-IEANTN.Li (Real.exp L)| ≤ envelope f L := by
  have hJ := Spectral076.actual_J_profile rh hN hI f (by linarith : (24:ℝ)≤L) hpsi
  have hQ := actual_remainder_effective rh hN hI hB hL
  have hQ0 := RHContinuation.Ramanujan.actual_prime_power_nonnegative (Real.exp_pos L)
  have htri := abs_sub_le (riemannPrimeCounting (Real.exp L)-IEANTN.li (Real.exp L))
    (0:ℝ) (riemannPrimeCounting (Real.exp L)-primeCounting (Real.exp L))
  simp only [sub_zero,zero_sub,abs_neg,abs_of_nonneg hQ0] at htri
  have he : primeCounting (Real.exp L)-IEANTN.li (Real.exp L) =
      (riemannPrimeCounting (Real.exp L)-IEANTN.li (Real.exp L))-
        (riemannPrimeCounting (Real.exp L)-primeCounting (Real.exp L)) := by ring
  have hp : |primeCounting (Real.exp L)-IEANTN.li (Real.exp L)| ≤
      Real.exp (L/2)/L*f L+Spectral076.profile L+effectiveRemainder L := by
    rw [he]
    linarith
  have hoff := actual_li_Li_offset (Real.one_lt_exp_iff.mpr (by linarith : (0:ℝ)<L))
  have h2 := RHLimit.PurePi.li_two_bounds
  have he' : primeCounting (Real.exp L)-IEANTN.Li (Real.exp L) =
      (primeCounting (Real.exp L)-IEANTN.li (Real.exp L))+IEANTN.li 2 := by linarith
  rw [he']
  have ha := abs_add_le (primeCounting (Real.exp L)-IEANTN.li (Real.exp L)) (IEANTN.li 2)
  rw [abs_of_nonneg h2.1] at ha
  unfold envelope
  linarith

theorem actual_box_pi_log (rh : RiemannHypothesis)
    (hN : NicolasContinuation.SourceNicolas119) (hI : SourceIntegratedPsi)
    (hB : RHOcticPush.BPTSourceEndpoint.SourceBPTOffOrdinate)
    {L : ℝ} (hL : 35 ≤ L) :
    |primeCounting (Real.exp L)-IEANTN.Li (Real.exp L)| ≤
      envelope RHOcticPush.BoxTail.improvedBound L := by
  have he := RHOcticPush.BoxPerron.box_explicit_formula hI
  have hz := RHOcticPush.BoxZero.box_zero_estimate_offOrdinate hN hB
  have hp := RHOcticPush.BoxTail.actual_psi_improved rh he hz
    RHOcticPush.BoxGamma.first_moment RHOcticPush.BoxGamma.second_moment_identity
    (Real.exp L) (Real.exp_le_exp.mpr hL)
  rw [Real.log_exp] at hp
  exact actual_pi_feedback rh hN hI hB RHOcticPush.BoxTail.improvedBound hL hp

theorem actual_box_pi (rh : RiemannHypothesis)
    (hN : NicolasContinuation.SourceNicolas119) (hI : SourceIntegratedPsi)
    (hB : RHOcticPush.BPTSourceEndpoint.SourceBPTOffOrdinate)
    {x : ℝ} (hx : Real.exp 35 ≤ x) :
    |primeCounting x-IEANTN.Li x| ≤ envelope RHOcticPush.BoxTail.improvedBound (Real.log x) := by
  have hx0 : 0 < x := (Real.exp_pos 35).trans_le hx
  have hL : 35 ≤ Real.log x := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 35) hx
  simpa only [Real.exp_log hx0] using actual_box_pi_log rh hN hI hB hL

theorem actual_box_interval (rh : RiemannHypothesis)
    (hN : NicolasContinuation.SourceNicolas119) (hI : SourceIntegratedPsi)
    (hB : RHOcticPush.BPTSourceEndpoint.SourceBPTOffOrdinate)
    {A B : ℝ} (hA : 35 ≤ A) (hBB : 35 ≤ B) :
    IEANTN.Li (Real.exp B)-IEANTN.Li (Real.exp A)-
      envelope RHOcticPush.BoxTail.improvedBound A-envelope RHOcticPush.BoxTail.improvedBound B ≤
      primeCounting (Real.exp B)-primeCounting (Real.exp A) := by
  have ha := (abs_le.mp (actual_box_pi_log rh hN hI hB hA)).2
  have hb := (abs_le.mp (actual_box_pi_log rh hN hI hB hBB)).1
  linarith

#print axioms envelope_le_old
#print axioms envelope_eq_old
#print axioms envelope_le_raw
#print axioms envelope_eq_min
#print axioms envelope_lt_simplified
#print axioms simplified_envelope_gain
#print axioms envelope_strict_gain
#print axioms actual_pi_feedback
#print axioms actual_box_pi_log
#print axioms actual_box_pi
#print axioms actual_box_interval
end RHOcticPush.PrimeSquareFeedback
