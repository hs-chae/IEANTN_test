/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import BoxImproved
import EvolvedPi
import GMPair
import NicolasBlock
import IEANTN.Nodes.RHSmoothing.v2.Conclusions
import IEANTN.Nodes.RHPrimeCounting.v1.Conclusions
import IEANTN.Nodes.RHPrimeCounting.v3.Conclusions
import IEANTN.Nodes.Nicolas.v1.Conclusions
import IEANTN.Nodes.Nicolas.v2.Conclusions
import IEANTN.Nodes.Lcm.v5.Conclusions

/-! Typed proofs of new canonical edges. No Challenge module is imported.
All numerical providers are actual proved source/model contracts; the remaining
analytic and literature assumptions are the named binders below. -/
namespace RHOcticPush.Integration
open Real Set MeasureTheory IEANTN RHContinuation.Ramanujan RHLimit.PrimePower
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Ordinary-pi transport actually consumes the new typed GM conclusion. -/
theorem pi_from_transfer (hT : RHPrimeCounting.v3.refined_transfer)
    (f : ℝ → ℝ) {L : ℝ} (hL : 12 ≤ L)
    (hpsi : |Chebyshev.psi (exp L)-exp L| ≤ sqrt (exp L)*f L) :
    |primeCounting (exp L)-IEANTN.Li (exp L)| ≤ RHOcticPush.Pi.envelope f L := by
  have h0 : 0<L := by linarith
  have hg := hT (exp L) (exp_le_exp.mpr hL)
  change |riemannPrimeCounting (exp L)-IEANTN.li (exp L)-
      (Chebyshev.psi (exp L)-exp L)/log (exp L)| ≤
    RHOcticPush.GM.evolvedBound (exp L) at hg
  rw [log_exp] at hg
  have hp : |(Chebyshev.psi (exp L)-exp L)/L| ≤ exp (L/2)/L*f L := by
    rw [abs_div,abs_of_pos h0]
    have h := div_le_div_of_nonneg_right hpsi h0.le
    rw [← Real.exp_half] at h
    convert! h using 1 <;> ring
  have he : riemannPrimeCounting (exp L)-IEANTN.li (exp L) =
      (riemannPrimeCounting (exp L)-IEANTN.li (exp L)-
        (Chebyshev.psi (exp L)-exp L)/L)+(Chebyshev.psi (exp L)-exp L)/L := by ring
  have hj : |riemannPrimeCounting (exp L)-IEANTN.li (exp L)| ≤
      RHOcticPush.GM.evolvedBound (exp L)+exp (L/2)/L*f L := by
    rw [he]
    exact (abs_add_le _ _).trans (add_le_add hg hp)
  have hq := actual_remainder_elementary (by linarith : (2:ℝ)≤L)
  have hq0 := actual_prime_power_nonnegative (exp_pos L)
  have hepi : primeCounting (exp L)-IEANTN.li (exp L) =
      (riemannPrimeCounting (exp L)-IEANTN.li (exp L))-
      (riemannPrimeCounting (exp L)-primeCounting (exp L)) := by ring
  have htri := abs_sub_le (riemannPrimeCounting (exp L)-IEANTN.li (exp L)) (0:ℝ)
    (riemannPrimeCounting (exp L)-primeCounting (exp L))
  simp only [sub_zero,zero_sub,abs_neg,abs_of_nonneg hq0] at htri
  have hpi : |primeCounting (exp L)-IEANTN.li (exp L)| ≤
      RHOcticPush.GM.evolvedBound (exp L)+exp (L/2)/L*f L+elementaryRemainder L := by
    rw [hepi]
    linarith
  have hoff := actual_li_Li_offset (one_lt_exp_iff.mpr (by linarith : (0:ℝ)<L))
  have h2 := RHLimit.PurePi.li_two_bounds
  have he2 : primeCounting (exp L)-IEANTN.Li (exp L) =
      (primeCounting (exp L)-IEANTN.li (exp L))+IEANTN.li 2 := by linarith
  rw [he2]
  have ht := abs_add_le (primeCounting (exp L)-IEANTN.li (exp L)) (IEANTN.li 2)
  rw [abs_of_nonneg h2.1] at ht
  unfold RHOcticPush.Pi.envelope
  linarith

/-- The correlated bound reuses the typed evolved endpoint certificate. -/
theorem pair_from_transfer (hRH : RH.v1.hypothesis)
    (hGM : RHPrimeCounting.v1.gm_source) (hT : RHPrimeCounting.v3.refined_transfer) :
    RHPrimeCounting.v3.paired_transfer := by
  intro K y x hK0 hK hy hyx
  have he15 : (3:ℝ)≤exp (15:ℝ) := by interval_decide 80 (trust := kernel)
  have hy3 : (3:ℝ)≤y := he15.trans hy
  have hy1 : 1<y := by linarith
  have hi := actual_gm_weighted_error hRH hGM hy3 hyx
  have hc := actual_riemann_compensation hy1 hyx
  have hd : RHPrimeCounting.v3.error x-RHPrimeCounting.v3.error y ≤ gmTransport y x := by
    unfold RHPrimeCounting.v3.error
    rw [hc]
    exact (le_abs_self _).trans hi
  have hmin : RHPrimeCounting.v3.evolvedCorrection y ≤
      (1551/100:ℝ)+RHPrimeCounting.v3.leading 5 y := by
    unfold RHPrimeCounting.v3.evolvedCorrection
    rw [if_pos hy]
    exact min_le_right _ _
  have hey := (hT y ((exp_le_exp.mpr (show (12:ℝ)≤15 by norm_num)).trans hy)).trans hmin
  have hney := (neg_le_abs (RHPrimeCounting.v3.error y)).trans hey
  have ht := RHOcticPush.GM.transport_upper (b:=5) (H:=15)
    (by norm_num) (by norm_num) (by norm_num) hy hyx
  have hkd := mul_le_mul_of_nonneg_left hd hK0
  have hke := mul_le_mul_of_nonneg_left hney (sub_nonneg.mpr hK)
  have hkt := mul_le_mul_of_nonneg_left ht hK0
  change K*RHPrimeCounting.v3.error x-exp 1*RHPrimeCounting.v3.error y ≤
    K*(RHOcticPush.GM.leading 5 x-RHOcticPush.GM.leading 5 y+
      2*gmEnvelope y*gmWeight y+(919/500:ℝ)/log y)+
      (exp 1-K)*((1551/100:ℝ)+RHOcticPush.GM.leading 5 y)
  change -RHPrimeCounting.v3.error y ≤ (1551/100:ℝ)+RHOcticPush.GM.leading 5 y at hney
  have hke' := mul_le_mul_of_nonneg_left hney (sub_nonneg.mpr hK)
  nlinarith
end RHOcticPush.Integration

namespace RHSmoothing.v2
set_option maxHeartbeats 0
/-- Actual same-source numerical/analytic provider, not an assumed output. -/
theorem challenge_box_psi (rh : RH.v1.hypothesis)
    (hef : RHSmoothingInputs.v1.box_explicit_formula)
    (hz : RHSmoothingInputs.v1.box_zero_estimate)
    (hfirst : BoxMellinInputs.v1.first_moment)
    (hsecond : BoxMellinInputs.v1.second_moment_identity) : box_psi :=
  RHOcticPush.BoxTail.actual_psi_improved rh hef hz hfirst hsecond

theorem challenge_box_gain : box_gain := RHOcticPush.BoxTail.envelope_gain
end RHSmoothing.v2

namespace RHPrimeCounting.v3
open Real IEANTN RHOcticPush.Integration
set_option maxHeartbeats 0

theorem challenge_refined_transfer (rh : RH.v1.hypothesis)
    (hg : RHPrimeCounting.v1.gm_source) (hp : Buthe.v1.theorem_2_psi)
    (hj : Buthe.v1.theorem_2_li_minus_riemann_pi) : refined_transfer :=
  fun _ hx => RHOcticPush.GM.actual_J_evolved rh hg hp hj hx

theorem challenge_transfer_gain : transfer_gain :=
  ⟨RHOcticPush.GM.preserves_old,fun _ hx => RHOcticPush.GM.evolved_strict hx⟩

theorem challenge_paired_transfer (rh : RH.v1.hypothesis)
    (hg : RHPrimeCounting.v1.gm_source) (ht : refined_transfer) : paired_transfer :=
  pair_from_transfer rh hg ht

theorem challenge_box_Li (ht : refined_transfer) (hb : RHSmoothing.v2.box_psi) : box_Li := by
  intro L hL
  have hpsi := hb (exp L) (exp_le_exp.mpr hL)
  rw [Real.log_exp] at hpsi
  exact pi_from_transfer ht IEANTN.RHOcticEvolution.boxBound (by linarith) hpsi

theorem challenge_ch_Li (ht : refined_transfer) (hc : RHSmoothing.v1.recovered_ch_psi) :
    ch_Li := by
  intro L hL
  have hpsi := hc (exp L) (exp_le_exp.mpr hL)
  rw [Real.log_exp,mul_comm] at hpsi
  exact pi_from_transfer ht IEANTN.RHSmoothing.chBound (by linarith) hpsi

theorem challenge_box_interval (hi : box_Li) : box_interval := by
  intro A B hA hAB
  have ha := (abs_le.mp (hi A hA)).2
  have hb := (abs_le.mp (hi B (hA.trans hAB))).1
  linarith
end RHPrimeCounting.v3

namespace Nicolas.v2
open Real NicolasContinuation
set_option maxHeartbeats 0

theorem challenge_spectral_four (rh : RH.v1.hypothesis)
    (h119 : Nicolas.v1.spectral_bound) : spectral_four :=
  fun _ hx => RHOcticPush.Nicolas.spectral_four rh h119 hx

/-- The actual arithmetic edge consumes the new spectral conclusion. -/
theorem challenge_product_four (rh : RH.v1.hypothesis)
    (h219 : Nicolas.v1.log_f_upper_full) (hs : spectral_four) : product_four := by
  intro x hx
  have hx2 : 599<x^2 := by nlinarith
  have hx3 : 599<x^3 := by nlinarith [sq_nonneg x]
  have hx4 : 599<x^4 := by nlinarith [sq_nonneg (x^2)]
  have h1 := RHOcticPush.Nicolas.retains_phase rh h219 hx
  have h2 := RHOcticPush.Nicolas.retains_phase rh h219 hx2
  have h3 := RHOcticPush.Nicolas.retains_phase rh h219 hx3
  have h4 := RHOcticPush.Nicolas.retains_phase rh h219 hx4
  have hp := hs x (by linarith : (0:ℝ)<x)
  change RHOcticPush.Nicolas.fourEnvelope x ≤
    4*RHOcticPush.Nicolas.scaledLogProduct x+
    3*RHOcticPush.Nicolas.scaledLogProduct (x^2)+
    2*RHOcticPush.Nicolas.scaledLogProduct (x^3)+
    RHOcticPush.Nicolas.scaledLogProduct (x^4)
  unfold RHOcticPush.Nicolas.fourEnvelope
  change -(5/2:ℝ)*beta ≤ 4*W x+3*W (x^2)+2*W (x^3)+W (x^4) at hp
  linarith

theorem challenge_product_block (hi : product_four) : product_block := by
  change ∀ x : ℝ, 599<x → ∃ k : ℕ, k∈({1,2,3,4}:Finset ℕ) ∧
    2-beta/4-penalty (x^k) ≤ scaledLogProduct (x^k)
  intro x hx
  have hsum := hi x hx
  have h : 2-beta/4-penalty x≤ scaledLogProduct x ∨
      2-beta/4-penalty (x^2)≤ scaledLogProduct (x^2) ∨
      2-beta/4-penalty (x^3)≤ scaledLogProduct (x^3) ∨
      2-beta/4-penalty (x^4)≤ scaledLogProduct (x^4) := by
    by_contra h
    push_neg at h
    rcases h with ⟨h1,h2,h3,h4⟩
    change 20-(5/2:ℝ)*beta-4*penalty x-3*penalty (x^2)-2*penalty (x^3)-penalty (x^4) ≤
      4*scaledLogProduct x+3*scaledLogProduct (x^2)+2*scaledLogProduct (x^3)+
      scaledLogProduct (x^4) at hsum
    linarith
  rcases h with h|h|h|h
  · exact ⟨1,by simp,by simpa using h⟩
  · exact ⟨2,by simp,h⟩
  · exact ⟨3,by simp,h⟩
  · exact ⟨4,by simp,h⟩

theorem challenge_four_gain : four_gain := RHOcticPush.Nicolas.four_strictly_improves
end Nicolas.v2

namespace Lcm.v5
open Real

theorem challenge_box_growth (hi : RHSmoothing.v2.box_psi) : box_growth := by
  intro n hn
  simpa only [Chebyshev.psi_eq_log_lcmUpto] using hi n hn

theorem challenge_recovered_growth (hi : RHSmoothing.v1.recovered_ch_psi) : recovered_growth := by
  intro n hn
  simpa only [Chebyshev.psi_eq_log_lcmUpto] using hi n hn
end Lcm.v5

#print axioms RHSmoothing.v2.challenge_box_psi
#print axioms RHPrimeCounting.v3.challenge_paired_transfer
#print axioms RHPrimeCounting.v3.challenge_box_Li
#print axioms RHPrimeCounting.v3.challenge_box_interval
#print axioms Nicolas.v2.challenge_product_four
#print axioms Nicolas.v2.challenge_product_block
#print axioms Lcm.v5.challenge_box_growth
