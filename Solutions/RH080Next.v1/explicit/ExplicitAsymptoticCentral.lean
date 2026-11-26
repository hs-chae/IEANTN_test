/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitAsymptoticAllowances
import ExplicitMellinLower
import ExplicitCentralPrimes
import ActualArithmeticSplit

set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open Real Set Filter MeasureTheory
open scoped Topology
namespace RH080Next.Explicit

def asymptoticNormalizedLower (nodes : List ℚ) (m : ℕ) (M U c t : ℝ) : ℝ :=
  (poleScale c t/t)*nodalF0 nodes m-U/2-nodalSignedLogUpper nodes m (3/8)/t-2/t-
    (poleScale c t*(halfLogWidth c t/2)^2*nodalMu2Upper nodes m)/t-
    (eventualWingLead c (radius nodes m) t/t)*IEANTN.CMSFunctional.positiveLeak (affineSpectrum nodes m)-
    (eventualWingEntrance c (radius nodes m) t/t)*nodalH nodes m-
    Primal.primePowerWindowAllowance M (t+halfLogWidth c t) (radius nodes m*halfLogWidth c t)/t

theorem asymptoticNormalizedLower_tendsto (nodes : List ℚ) (m : ℕ) (M U c : ℝ) (hc : 0<c) :
    Tendsto (asymptoticNormalizedLower nodes m M U c) atTop
      (𝓝 ((c*(nodalF0 nodes m-4*IEANTN.CMSFunctional.positiveLeak (affineSpectrum nodes m))-U)/2)) := by
  have hPole := (poleScale_div_tendsto c hc).mul_const (nodalF0 nodes m)
  have hS := (tendsto_const_nhds (x := nodalSignedLogUpper nodes m (3/8))).div_atTop (show Tendsto (fun t : ℝ => t) atTop atTop from tendsto_id)
  have hTwo := (tendsto_const_nhds (x := (2:ℝ))).div_atTop (show Tendsto (fun t : ℝ => t) atTop atTop from tendsto_id)
  have hPL := (eventual_pole_loss_tendsto_zero c (nodalMu2Upper nodes m) hc).mul tendsto_inv_atTop_zero
  have hLead := (eventual_wing_lead_div_tendsto c (radius nodes m) hc).mul_const
    (IEANTN.CMSFunctional.positiveLeak (affineSpectrum nodes m))
  have hEnt := ((eventual_wing_entrance_tendsto c (radius nodes m)).mul tendsto_inv_atTop_zero).mul_const (nodalH nodes m)
  have hPP := (eventual_primepower_allowance_tendsto_zero c (radius nodes m) M hc).mul tendsto_inv_atTop_zero
  have h := ((((((hPole.sub_const (U/2)).sub hS).sub hTwo).sub hPL).sub hLead).sub hEnt).sub hPP
  have he : c/2*nodalF0 nodes m-U/2-0-0-0*0-2*c*IEANTN.CMSFunctional.positiveLeak (affineSpectrum nodes m)-8*0*nodalH nodes m-0*0 =
    (c*(nodalF0 nodes m-4*IEANTN.CMSFunctional.positiveLeak (affineSpectrum nodes m))-U)/2 := by ring
  rw [he] at h
  change Tendsto (fun t : ℝ => asymptoticNormalizedLower nodes m M U c t) atTop _
  simpa only [asymptoticNormalizedLower,div_eq_mul_inv] using h

/-- The complete ACTUAL Mellin and arithmetic sums imply an eventual central
count lower bound for arbitrary fixed c>0, including support seven. No BR
support-five population theorem is assumed or obtained by an invalid cutoff
rescaling. The generic named analytic source contracts remain explicit. -/
theorem eventual_actual_central_normalized_lower
    (hBR : SourceBRFourierNormStrip) (hCMS : SourceCMSGuinandWeil)
    (hDigamma : SourceDLMFDigammaIntegral)
    (hZero : SourceCMSZeroPartialSummationProofScheme) (hCount : SourceCMSZeroCounting)
    (hEta : SourceDLMFRealEtaIntegral) (hMV : SourceMontgomeryVaughan) (hRH : RiemannHypothesis)
    (nodes : List ℚ) (m n : ℕ) (hm : 0<m) (hmn : m≤n)
    (hlen : nodes.length=5*n+1) (hlast : node nodes (5*n)=0)
    (hmN : m<nodes.length-1) (hR : radius nodes m≤10)
    (hA : nodalMassA0 nodes m≤2) (hV0 : nodalV0 nodes≤10) (hV1 : nodalV1 nodes m≤50)
    (M U c : ℝ) (hM : 0≤M) (hW : ∀ v : ℝ, |affineSpectrum nodes m v|≤M)
    (hU : (∫ u : ℝ, |inverseCosine (affineSpectrum nodes m) u|)≤U) (hc : 0<c) :
    ∀ᶠ t : ℝ in atTop, asymptoticNormalizedLower nodes m M U c t≤
      centralPrimeSum nodes m (halfLogWidth c t) t/t := by
  obtain ⟨T0,hT0e,hT09,hT010,hQ⟩ := cms_zero_count_root_exists
  have hn : 0<n := lt_of_lt_of_le hm hmn
  have hlen2 : 2≤nodes.length := by rw [hlen]; omega
  have hlast' : node nodes (nodes.length-1)=0 := by rw [hlen,Nat.add_sub_cancel]; exact hlast
  have hR0 : 0≤radius nodes m := by unfold radius; positivity
  have hU0 : 0≤U := (integral_nonneg (fun u : ℝ => abs_nonneg _)).trans hU
  have hA0 : 0≤nodalMassA0 nodes m := by unfold nodalMassA0; positivity
  have hgeom : Tendsto (fun t : ℝ => t+(1-radius nodes m)*halfLogWidth c t) atTop atTop :=
    tendsto_id.atTop_add ((halfLogWidth_tendsto_zero c).const_mul (1-radius nodes m))
  have hGeomEvent : ∀ᶠ t : ℝ in atTop, log 4<t+(1-radius nodes m)*halfLogWidth c t :=
    hgeom.eventually (eventually_gt_atTop (log 4))
  have hSmall : ∀ᶠ t : ℝ in atTop, halfLogWidth c t<(1/50000000:ℝ) :=
    (tendsto_order.1 (halfLogWidth_tendsto_zero c)).2 _ (by norm_num)
  filter_upwards [eventually_ge_atTop (42:ℝ),hGeomEvent,hSmall,log_inverse_width_eventually_le c hc] with t ht hgeom hsmall hlog
  let d := halfLogWidth c t
  let L := t+d
  let R := radius nodes m
  have ht0 : 0<t := by linarith
  have hd : 0<d := (halfLogWidth_squeeze c t hc ht0).1
  have hpositive : R*d<L := by
    have hl4 : 0<log (4:ℝ) := log_pos (by norm_num)
    dsimp [R,L,d]
    linarith
  have hY : 4<exp (L-R*d) := by
    rw [←exp_log (by norm_num : (0:ℝ)<4)]
    apply exp_lt_exp.mpr
    dsimp [L,R,d]
    linarith
  have hSqrt : 2≤sqrt (exp (L-R*d)) := by
    have h := sqrt_le_sqrt hY.le
    norm_num at h
    exact h
  have hDen : 30≤sqrt (exp (L-R*d))*(exp (L-R*d)^2-1) := by
    have hh : 15≤exp (L-R*d)^2-1 := by nlinarith
    nlinarith
  have hTriv := (trivial_integral_bound nodes m hlen2 hm d L hd hpositive).2
  have hTriv1 : |∫ y in exp (L-R*d)..exp (L+R*d),trivialYIntegrand nodes m d L y|≤1 := by
    apply hTriv.trans
    apply (div_le_iff₀ (by linarith : 0<sqrt (exp (L-R*d))*(exp (L-R*d)^2-1))).mpr
    have hsmall' : d≤1 := by dsimp [d]; linarith
    have hmul := mul_le_mul hsmall' hA hA0 (by norm_num : (0:ℝ)≤1)
    norm_num at hmul
    linarith
  have hPoleSmall : |d/2| * radius nodes m≤1 := by
    rw [abs_of_pos (by positivity)]
    have hmul := mul_le_mul_of_nonneg_left hR (by positivity : (0:ℝ)≤d/2)
    dsimp [d] at *
    nlinarith
  have hPole := mellin_pole_lower nodes m hlen2 hm hlast' d L hd.le hPoleSmall
  obtain ⟨_,hZeroBound⟩ := affine_zero_estimate hZero hCount hRH hEta nodes m hlen2 hm hlast'
    d L T0 U hd (by dsimp [d]; linarith) hT0e hT010 hQ hU
  have hAllow := zero_allowance_lt nodes m hR hA hV0 hV1 d T0 hd (by dsimp [d]; linarith)
    ((exp_pos 1).trans_le hT0e) hT010.le
  have hZeroSimple : ‖(d:ℂ)*(∑' ρ : CMSZeroIndex,realZeroFamily nodes m d L ρ)‖≤
      U*t/2+nodalSignedLogUpper nodes m (3/8)+1 := by
    have hmul := mul_le_mul_of_nonneg_left hlog hU0
    dsimp [d] at *
    nlinarith
  obtain ⟨_,_,hEq⟩ := source_RH_affine_mellin_identity hBR hCMS hDigamma hRH
    nodes m n hm hmn hlen hlast d L hd hpositive
  have hre := congrArg Complex.re hEq
  simp only [Complex.ofReal_re,Complex.sub_re] at hre
  have hRe := Complex.re_le_norm ((d:ℂ)*(∑' ρ : CMSZeroIndex,realZeroFamily nodes m d L ρ))
  have hpEq : d*exp (L/2)=poleScale c t := by unfold poleScale; dsimp [L]; rw [show (t+d)/2=t/2+d/2 by ring]
  rw [hpEq] at hre hPole
  have hTrivLe := le_abs_self (∫ y in exp (L-R*d)..exp (L+R*d),trivialYIntegrand nodes m d L y)
  have hFull := (Primal.actual_full_arithmetic_wing_bound hMV nodes m hlen2 hm hmN hlast' d L (exp (L/2)) hd hpositive
    (one_lt_exp_iff.mpr (by dsimp [L]; positivity))).2
  have hPP := (Primal.actual_nonprimeMangoldt_window_bound nodes m hlen2 hm d L M hd hM
    (by dsimp [L]; positivity) hW).2
  have hCenter : Primal.centralPrimePart nodes m d L=centralPrimeSum nodes m d t := by
    unfold Primal.centralPrimePart centralPrimeSum
    dsimp [L]
    rw [show t+d-d=t by ring,show t+d+d=t+2*d by ring]
  rw [hCenter] at hFull
  change _ ≤ centralPrimeSum nodes m d t+eventualWingLead c R t*IEANTN.CMSFunctional.positiveLeak (affineSpectrum nodes m)+
    eventualWingEntrance c R t*nodalH nodes m+_ at hFull
  have hRaw : poleScale c t*nodalF0 nodes m-U*t/2-nodalSignedLogUpper nodes m (3/8)-2-
      poleScale c t*(d/2)^2*nodalMu2Upper nodes m-
      eventualWingLead c R t*IEANTN.CMSFunctional.positiveLeak (affineSpectrum nodes m)-
      eventualWingEntrance c R t*nodalH nodes m-
      Primal.primePowerWindowAllowance M L (R*d)≤centralPrimeSum nodes m d t := by
    nlinarith
  have hNorm : asymptoticNormalizedLower nodes m M U c t =
      (poleScale c t*nodalF0 nodes m-U*t/2-nodalSignedLogUpper nodes m (3/8)-2-
        poleScale c t*(d/2)^2*nodalMu2Upper nodes m-
        eventualWingLead c R t*IEANTN.CMSFunctional.positiveLeak (affineSpectrum nodes m)-
        eventualWingEntrance c R t*nodalH nodes m-
        Primal.primePowerWindowAllowance M L (R*d))/t := by
    unfold asymptoticNormalizedLower
    dsimp [d,L,R]
    field_simp
    <;> ring
  rw [hNorm]
  exact div_le_div_of_nonneg_right hRaw ht0.le

#print axioms asymptoticNormalizedLower_tendsto
#print axioms eventual_actual_central_normalized_lower
end RH080Next.Explicit
