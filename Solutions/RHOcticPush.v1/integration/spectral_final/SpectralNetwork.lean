import SpectralComparison
import BoxFullNetwork
import IEANTN.Nodes.RHPrimeCounting.v5.Conclusions

/-! Source-reduced signed spectral transport in the canonical IEANTN graph.
The complete new Box pi and count bounds use RH/Perron/Nicolas/BPT only;
no GM or either old Büthe transfer input is assumed or hidden in the body. -/
open Real IEANTN Set
open RHLimit.PrimePower RHOcticPush.BoxPerron RHContinuation.Ramanujan
set_option maxHeartbeats 0

namespace RHOcticPush.SpectralCanonical
/-- The literal published primitive starts at0; the proved normalization is
consumed when converting the canonical general source into the formal model. -/
theorem canonical_source (h : IntegratedPerron.v1.formula) : SourceIntegratedPsi := by
  apply integrated_source_normalized
  obtain ⟨C,hC⟩ := h
  refine ⟨C,?_⟩
  intro x hx
  refine ⟨(hC x hx).1,?_⟩
  rw [psi1_integral_from_zero]
  exact (hC x hx).2
end RHOcticPush.SpectralCanonical

namespace RHPrimeCounting.v5

theorem challenge_compensation_profile (rh : RH.v1.hypothesis)
    (hi : IntegratedPerron.v1.formula) (hn : Nicolas.v1.spectral_bound) :
    compensation_profile := fun _ hx => RHOcticPush.Spectral076.actual_compensation_profile
      rh hn (RHOcticPush.SpectralCanonical.canonical_source hi) hx

theorem challenge_compensation_076 (ht : compensation_profile) : compensation_076 := by
  intro x hx
  have hx0 : 0 < x := (exp_pos 24).trans_le hx
  have hL : 24 ≤ log x := by simpa only [log_exp] using log_le_log (exp_pos 24) hx
  have hp := (ht x hx).trans_lt (RHOcticPush.Spectral076.profile_lt_076 hL)
  simpa only [Real.exp_half,Real.exp_log hx0] using hp

theorem challenge_compensation_055 (ht : compensation_profile) : compensation_055 := by
  intro x hx
  have hx0 : 0 < x := (exp_pos 35).trans_le hx
  have hL : 35 ≤ log x := by simpa only [log_exp] using log_le_log (exp_pos 35) hx
  have h24 := (exp_le_exp.mpr (show (24:ℝ)≤35 by norm_num)).trans hx
  have hp := (ht x h24).trans_lt (RHOcticPush.Spectral076.profile_lt_055 hL)
  simpa only [Real.exp_half,Real.exp_log hx0] using hp

/-- The arithmetic ordinary-pi edge consumes only the typed actual compensated
profile and a typed psi provider. The prime-power and Li2 corrections are real. -/
theorem challenge_ordinary_transfer (ht : compensation_profile) : ordinary_transfer := by
  intro f L hL hpsi
  have h0 : 0 < L := by linarith
  have hd := ht (exp L) (exp_le_exp.mpr hL)
  change |riemannPrimeCounting (exp L)-IEANTN.li (exp L)-
      (Chebyshev.psi (exp L)-exp L)/log (exp L)| ≤ profile (log (exp L)) at hd
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
      exp (L/2)/L*f L+profile L := by linarith
  have hq := actual_remainder_elementary (by linarith : (2:ℝ)≤L)
  have hq0 := actual_prime_power_nonnegative (exp_pos L)
  have htri := abs_sub_le (riemannPrimeCounting (exp L)-IEANTN.li (exp L))
    (0:ℝ) (riemannPrimeCounting (exp L)-primeCounting (exp L))
  simp only [sub_zero,zero_sub,abs_neg,abs_of_nonneg hq0] at htri
  have hpi : |primeCounting (exp L)-IEANTN.li (exp L)| ≤
      exp (L/2)/L*f L+profile L+elementaryRemainder L := by
    have he : primeCounting (exp L)-IEANTN.li (exp L) =
        (riemannPrimeCounting (exp L)-IEANTN.li (exp L))-
          (riemannPrimeCounting (exp L)-primeCounting (exp L)) := by ring
    rw [he]
    linarith
  have hoff := actual_li_Li_offset (Real.one_lt_exp_iff.mpr h0)
  have h2 := RHLimit.PurePi.li_two_bounds
  have he : primeCounting (exp L)-IEANTN.Li (exp L) =
      (primeCounting (exp L)-IEANTN.li (exp L))+IEANTN.li 2 := by linarith
  rw [he]
  have hh := abs_add_le (primeCounting (exp L)-IEANTN.li (exp L)) (IEANTN.li 2)
  rw [abs_of_nonneg h2.1] at hh
  unfold piEnvelope
  change |primeCounting (exp L)-IEANTN.li (exp L)+IEANTN.li 2| ≤
    exp (L/2)/L*f L+profile L+elementaryRemainder L+2
  linarith

theorem challenge_whole_gain : whole_gain :=
  fun f _ hL => RHOcticPush.Spectral076.piEnvelope_strict_gain f hL

theorem challenge_effective_min (hg : whole_gain) : effective_min := by
  intro f L hL
  unfold effectiveEnvelope
  exact min_eq_right (by have hh := hg f L hL; linarith)

theorem challenge_box_Li (ht : ordinary_transfer) (hp : RHSmoothing.v3.box_psi)
    (hm : effective_min) : box_Li := by
  intro L hL
  rw [hm _ L (by linarith)]
  apply ht IEANTN.RHOcticEvolution.boxBound L (by linarith)
  have h := hp (exp L) (exp_le_exp.mpr hL)
  simpa only [log_exp] using h

theorem challenge_box_interval (hp : box_Li) : box_interval := by
  intro A B hA hAB
  have ha := (abs_le.mp (hp A hA)).2
  have hb := (abs_le.mp (hp B (hA.trans hAB))).1
  linarith
theorem challenge_ch_Li (ht : ordinary_transfer) (hp : RHSmoothing.v1.recovered_ch_psi)
    (hm : effective_min) : ch_Li := by
  intro L hL
  rw [hm _ L (by linarith)]
  apply ht IEANTN.RHSmoothing.chBound L (by linarith)
  have h := hp (exp L) (exp_le_exp.mpr hL)
  simpa only [log_exp,mul_comm] using h

theorem challenge_ch_interval (hp : ch_Li) : ch_interval := by
  intro A B hA hAB
  have ha := (abs_le.mp (hp A hA)).2
  have hb := (abs_le.mp (hp B (hA.trans hAB))).1
  linarith
end RHPrimeCounting.v5

namespace RHOcticPush.Network
/-- Every actual Box and signed spectral provider is constructed. These FOUR
inputs replace the former Box pi chain's additional GM and two Büthe inputs. -/
theorem fully_derived_spectral_box_network (rh : RH.v1.hypothesis)
    (hi : IntegratedPerron.v1.formula) (hn : Nicolas.v1.spectral_bound)
    (hb : BPTOffOrdinate.v1.bound) :
    RHPrimeCounting.v5.compensation_profile ∧ RHPrimeCounting.v5.compensation_076 ∧
    RHPrimeCounting.v5.compensation_055 ∧ RHSmoothing.v3.box_psi ∧ Lcm.v6.box_growth ∧
    RHPrimeCounting.v5.box_Li ∧ RHPrimeCounting.v5.box_interval := by
  have ht := RHPrimeCounting.v5.challenge_compensation_profile rh hi hn
  have he := RHSmoothingInputs.v2.challenge_box_explicit_formula hi
  have hz := RHSmoothingInputs.v2.challenge_box_zero_estimate hn hb
  have hp := RHSmoothing.v3.challenge_box_psi rh he hz
    BoxMellinInputs.v2.challenge_first_moment BoxMellinInputs.v2.challenge_second_moment_identity
  have hm := RHPrimeCounting.v5.challenge_effective_min RHPrimeCounting.v5.challenge_whole_gain
  have hpi := RHPrimeCounting.v5.challenge_box_Li
    (RHPrimeCounting.v5.challenge_ordinary_transfer ht) hp hm
  exact ⟨ht,RHPrimeCounting.v5.challenge_compensation_076 ht,
    RHPrimeCounting.v5.challenge_compensation_055 ht,hp,Lcm.v6.challenge_box_growth hp,
    hpi,RHPrimeCounting.v5.challenge_box_interval hpi⟩
end RHOcticPush.Network

#print axioms RHPrimeCounting.v5.challenge_compensation_profile
#print axioms RHPrimeCounting.v5.challenge_compensation_076
#print axioms RHPrimeCounting.v5.challenge_compensation_055
#print axioms RHPrimeCounting.v5.challenge_ordinary_transfer
#print axioms RHPrimeCounting.v5.challenge_whole_gain
#print axioms RHPrimeCounting.v5.challenge_effective_min
#print axioms RHPrimeCounting.v5.challenge_box_Li
#print axioms RHPrimeCounting.v5.challenge_box_interval
#print axioms RHPrimeCounting.v5.challenge_ch_Li
#print axioms RHPrimeCounting.v5.challenge_ch_interval
#print axioms RHOcticPush.Network.fully_derived_spectral_box_network
