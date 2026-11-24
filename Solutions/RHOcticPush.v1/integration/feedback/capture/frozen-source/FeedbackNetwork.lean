import FeedbackCorollary
import SpectralNetwork
import IEANTN.Nodes.RHPrimeCounting.v6.Conclusions

/-! Actual typed program-independent mathematical propagation: J upper bound
feeds the real prime-square correction, then ordinary pi and its interval count.
Every final source provider uses exactly RH/Perron/Nicolas/BPT. -/
open Real IEANTN Set
open RHLimit.PrimePower RHOcticPush.BoxPerron RHContinuation.Ramanujan
namespace RHPrimeCounting.v6

theorem challenge_J_upper (rh : RH.v1.hypothesis)
    (hi : IntegratedPerron.v1.formula) (hn : Nicolas.v1.spectral_bound)
    (hb : BPTOffOrdinate.v1.bound) : J_upper := by
  intro L hL
  exact RHOcticPush.PrimeSquareFeedback.J_upper_log rh hn
    (RHOcticPush.SpectralCanonical.canonical_source hi) hb hL

/-- A genuine typed J_upper -> prime-power-feedback edge. No numerical Q
bound is assumed, and the lower-scale onset is checked before application. -/
theorem challenge_prime_power_feedback (hj : J_upper) : prime_power_feedback := by
  intro L hL
  unfold effectiveRemainder
  by_cases h70 : 70 ≤ L
  · rw [if_pos h70]
    apply le_min (actual_remainder_elementary (by linarith : (2:ℝ)≤L))
    have hx : (4:ℝ) ≤ exp L :=
      exp_two_ge_four.trans (exp_le_exp.mpr (by linarith : (2:ℝ)≤L))
    have hQ := remainder_upper_with_square hx
    have hJ := hj (L/2) (by linarith : (35:ℝ)≤L/2)
    have hq0 := actual_prime_power_nonnegative (exp_pos (L/2))
    have hp : primeCounting (exp (L/2)) ≤ Jupper (L/2) := by linarith
    have hs := div_le_div_of_nonneg_right hp (by norm_num : (0:ℝ)≤2)
    rw [←sqrt_exp_eq] at hs
    have he : (exp L)^(1/(3:ℝ))=exp (L/3) := by
      rw [←exp_mul]
      congr 1
      ring
    rw [he] at hQ
    have htail := mul_le_mul_of_nonneg_left (height_log_bound (by linarith : (2:ℝ)≤L))
      (exp_pos (L/3)).le
    unfold rawRemainder
    linarith [exp_pos (L/4)]
  · rw [if_neg h70]
    exact actual_remainder_elementary (by linarith : (2:ℝ)≤L)

theorem challenge_ordinary_transfer (ht : RHPrimeCounting.v5.compensation_profile) (hq : prime_power_feedback) : ordinary_transfer := by
  intro f L hL hpsi
  have h0 : 0 < L := by linarith
  have hd := ht (exp L) (exp_le_exp.mpr (by linarith : (24:ℝ)≤L))
  change |riemannPrimeCounting (exp L)-IEANTN.li (exp L)-
      (Chebyshev.psi (exp L)-exp L)/log (exp L)| ≤ RHPrimeCounting.v5.profile (log (exp L)) at hd
  rw [log_exp] at hd
  have hp : |(Chebyshev.psi (exp L)-exp L)/L| ≤ exp (L/2)/L*f L := by
    rw [abs_div,abs_of_pos h0]
    have hh := div_le_div_of_nonneg_right hpsi h0.le
    rw [←Real.exp_half] at hh
    convert! hh using 1 <;> ring
  have hj := abs_add_le
    (riemannPrimeCounting (exp L)-IEANTN.li (exp L)-(Chebyshev.psi (exp L)-exp L)/L)
    ((Chebyshev.psi (exp L)-exp L)/L)
  simp only [sub_add_cancel] at hj
  have hJ : |riemannPrimeCounting (exp L)-IEANTN.li (exp L)| ≤
      exp (L/2)/L*f L+RHPrimeCounting.v5.profile L := by linarith
  have hqq := hq L hL
  have hq0 := actual_prime_power_nonnegative (exp_pos L)
  have htri := abs_sub_le (riemannPrimeCounting (exp L)-IEANTN.li (exp L))
    (0:ℝ) (riemannPrimeCounting (exp L)-primeCounting (exp L))
  simp only [sub_zero,zero_sub,abs_neg,abs_of_nonneg hq0] at htri
  have hpi : |primeCounting (exp L)-IEANTN.li (exp L)| ≤
      exp (L/2)/L*f L+RHPrimeCounting.v5.profile L+effectiveRemainder L := by
    have he : primeCounting (exp L)-IEANTN.li (exp L) =
        (riemannPrimeCounting (exp L)-IEANTN.li (exp L))-
          (riemannPrimeCounting (exp L)-primeCounting (exp L)) := by ring
    rw [he]
    linarith only [htri,hqq,hJ]
  have hoff := actual_li_Li_offset (Real.one_lt_exp_iff.mpr h0)
  have h2 := RHLimit.PurePi.li_two_bounds
  have he : primeCounting (exp L)-IEANTN.Li (exp L) =
      (primeCounting (exp L)-IEANTN.li (exp L))+IEANTN.li 2 := by linarith
  rw [he]
  have hh := abs_add_le (primeCounting (exp L)-IEANTN.li (exp L)) (IEANTN.li 2)
  rw [abs_of_nonneg h2.1] at hh
  unfold piEnvelope
  change |primeCounting (exp L)-IEANTN.li (exp L)+IEANTN.li 2| ≤
    exp (L/2)/L*f L+RHPrimeCounting.v5.profile L+effectiveRemainder L+2
  linarith

theorem challenge_box_Li (ht : ordinary_transfer) (hp : RHSmoothing.v3.box_psi) :
    box_Li := by
  intro L hL
  apply ht RHOcticEvolution.boxBound L hL
  have h := hp (exp L) (exp_le_exp.mpr hL)
  simpa only [log_exp] using h

theorem challenge_box_interval (hp : box_Li) : box_interval := by
  intro A B hA hAB
  have ha := (abs_le.mp (hp A hA)).2
  have hb := (abs_le.mp (hp B (hA.trans hAB))).1
  linarith

theorem challenge_preserves_v5 (hm : RHPrimeCounting.v5.effective_min) : preserves_v5 := by
  intro f L hL
  rw [hm f L (by linarith)]
  exact RHOcticPush.PrimeSquareFeedback.envelope_le_old f L

theorem challenge_below70 : below70 := by
  intro f L hL
  exact RHOcticPush.PrimeSquareFeedback.envelope_eq_old hL f

theorem challenge_full_min : full_min := by
  intro f L hL
  exact RHOcticPush.PrimeSquareFeedback.envelope_eq_min hL f

theorem challenge_whole_gain : whole_gain := by
  intro f L hL
  exact RHOcticPush.PrimeSquareFeedback.envelope_strict_gain hL f

theorem challenge_clean_pi (hp : box_Li) : clean_pi := by
  intro x hx
  have hx0 : 0<x := (exp_pos 100).trans_le hx
  have hL : 100 ≤ log x := by simpa only [log_exp] using log_le_log (exp_pos 100) hx
  have h := (hp (log x) (by linarith)).trans_lt
    (RHOcticPush.PrimeSquareFeedback.envelope_clean hL)
  simpa only [exp_half,exp_log hx0] using h

theorem challenge_clean_gain : clean_gain :=
  RHOcticPush.PrimeSquareFeedback.clean_gain
end RHPrimeCounting.v6

namespace RHOcticPush.Network
/-- The same FOUR source providers construct every new actual numerical bound;
all desired J/Q/psi/ordinary-pi predicates are derived inside the proof. -/
theorem fully_derived_feedback_box_network (rh : RH.v1.hypothesis)
    (hi : IntegratedPerron.v1.formula) (hn : Nicolas.v1.spectral_bound)
    (hb : BPTOffOrdinate.v1.bound) :
    RHPrimeCounting.v6.J_upper ∧ RHPrimeCounting.v6.prime_power_feedback ∧
    RHPrimeCounting.v6.box_Li ∧ RHPrimeCounting.v6.box_interval ∧
    RHPrimeCounting.v6.clean_pi := by
  have hj := RHPrimeCounting.v6.challenge_J_upper rh hi hn hb
  have hq := RHPrimeCounting.v6.challenge_prime_power_feedback hj
  have ht := RHPrimeCounting.v5.challenge_compensation_profile rh hi hn
  have he := RHSmoothingInputs.v2.challenge_box_explicit_formula hi
  have hz := RHSmoothingInputs.v2.challenge_box_zero_estimate hn hb
  have hp := RHSmoothing.v3.challenge_box_psi rh he hz
    BoxMellinInputs.v2.challenge_first_moment BoxMellinInputs.v2.challenge_second_moment_identity
  have hpi := RHPrimeCounting.v6.challenge_box_Li
    (RHPrimeCounting.v6.challenge_ordinary_transfer ht hq) hp
  exact ⟨hj,hq,hpi,RHPrimeCounting.v6.challenge_box_interval hpi,
    RHPrimeCounting.v6.challenge_clean_pi hpi⟩
end RHOcticPush.Network

#print axioms RHPrimeCounting.v6.challenge_J_upper
#print axioms RHPrimeCounting.v6.challenge_prime_power_feedback
#print axioms RHPrimeCounting.v6.challenge_ordinary_transfer
#print axioms RHPrimeCounting.v6.challenge_box_Li
#print axioms RHPrimeCounting.v6.challenge_box_interval
#print axioms RHPrimeCounting.v6.challenge_preserves_v5
#print axioms RHPrimeCounting.v6.challenge_below70
#print axioms RHPrimeCounting.v6.challenge_full_min
#print axioms RHPrimeCounting.v6.challenge_whole_gain
#print axioms RHPrimeCounting.v6.challenge_clean_pi
#print axioms RHPrimeCounting.v6.challenge_clean_gain
#print axioms RHOcticPush.Network.fully_derived_feedback_box_network

