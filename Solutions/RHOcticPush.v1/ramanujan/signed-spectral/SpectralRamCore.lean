import PairedRamInterface
import SpectralFinal

/-! Additive Ramanujan synthesis from the actual signed spectral profile.
The accepted 607-billion / nine-input track remains unchanged. This module
exposes its different source package rather than treating it as matched-premise.
-/
namespace RHOcticPush.SpectralRam
open Real Set Finset IEANTN RamanujanPV.AnalyticTransition
open Ramanujan640 Ramanujan640.AnalyticBarrier RHContinuation.Ramanujan
open RHLimit.Ram620 RHOcticPush.Ram RHOcticPush.Correlated
open RHOcticPush.Spectral076 RHOcticPush.BoxPerron
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
set_option leancert.trust "kernel"

noncomputable def budget (k z : ℝ) : ℝ := k * profile z + exp 1 * profile (z - 1)

theorem actual_pair (rh : RiemannHypothesis)
    (hN : NicolasContinuation.SourceNicolas119) (hI : SourceIntegratedPsi)
    {k z : ℝ} (hk : 0 ≤ k) (hz : 25 ≤ z) :
    k * GM.error (exp z) - exp 1 * GM.error (exp (z - 1)) ≤ budget k z := by
  have hx := actual_compensation_profile rh hN hI
    (Real.exp_le_exp.mpr (by linarith : (24 : ℝ) ≤ z))
  have hy := actual_compensation_profile rh hN hI
    (Real.exp_le_exp.mpr (by linarith : (24 : ℝ) ≤ z - 1))
  simp only [Real.log_exp] at hx hy
  have hxu := (le_abs_self (GM.error (exp z))).trans hx
  have hyl := (neg_le_abs (GM.error (exp (z - 1)))).trans hy
  have h1 := mul_le_mul_of_nonneg_left hxu hk
  have h2 := mul_le_mul_of_nonneg_left hyl (Real.exp_pos 1).le
  unfold budget
  linarith

noncomputable def margin (k a b z : ℝ) : ℝ :=
  SharpBase.sharpBase z + k * F z * a - H z * b - (q z)^2 * Q z - T z * budget k z

theorem actual_margin (rh : RiemannHypothesis)
    (hN : NicolasContinuation.SourceNicolas119) (hI : SourceIntegratedPsi)
    (hTab : Buthe.v1.table_1_interval_bounds)
    (hL : Buthe.v1.theorem_2_li_minus_pi) (hU : Buthe.v1.theorem_2_li_gt_pi)
    {l u z k a b : ℝ} (hl : 27 ≤ l) (hu : u ≤ 42) (hlz : l ≤ z) (hzu : z ≤ u)
    (hcut : (480000000000 : ℝ) ≤ exp z) (hcap : exp z ≤ 640000000000)
    (hk0 : 0 ≤ k) (hkw : k ≤ 2 * pN 20 u)
    (ha : a ≤ -88 / 100 + lowerPowers l u)
    (hb : 68 / 100 + upperPowers (l - 1) ≤ b) : margin k a b z ≤ RamStudy.RG (exp z) := by
  have hz27 : (27 : ℝ) ≤ z := hl.trans hlz
  have hz0 : 0 < z := by linarith
  have hzm1 : 0 < z - 1 := by linarith
  have hz42 : z ≤ 42 := hzu.trans hu
  have hz2 : 2 ≤ exp z := exp_one_gt_two.le.trans (exp_le_exp.mpr (by linarith))
  have hc0 := (source_deficit_pos hU hz0 hz2 hz42).le
  have hcq := source_deficit_upper hL hz0 hz2 hz42
  have hsq := pow_le_pow_left₀ hc0 hcq 2
  have hF : 0 ≤ F z := by unfold F; positivity
  have hH : 0 ≤ H z := by unfold H; positivity
  have hQ : 0 ≤ Q z := by unfold Q; positivity
  have hT : 0 ≤ T z := by unfold T; positivity
  have hbase := SharpBase.actual_sharp_base hz27
  have hactual := actual_signed_gap (by linarith : 1 < z) hbase
    (le_refl (deficit z)) (le_refl (deficit (z - 1)))
  have hactual' : SharpBase.sharpBase z - H z * deficit (z - 1) +
      2 * RamStudy.w z * F z * deficit z - (deficit z)^2 * Q z ≤
      RamStudy.RG (exp z) := by
    convert hactual using 1 <;> unfold F H Q <;> ring
  have hw : pN 20 u ≤ RamStudy.w z :=
    (pN_antitone hz0 hzu 20).trans (by
      simpa only [actual_w_eq] using
        (actual_factorial_barrier26 (by linarith : 26 ≤ z)).1)
  have hkactual : k ≤ 2 * RamStudy.w z := by linarith
  have hkwc := mul_le_mul_of_nonneg_right hkactual (mul_nonneg hF hc0)
  have hsqQ := mul_le_mul_of_nonneg_right hsq hQ
  have ht := table1_bridge480 hTab hcut hcap
  have hpow := powers_lower hL (by linarith : 26 ≤ l) hlz hzu hu
  have hpow' := powers_upper hU (by linarith : 26 ≤ l - 1)
    (by linarith : l - 1 ≤ z - 1) (by linarith : z - 1 ≤ 42)
  have ha' : a ≤ psiDeficit z + primePart z := by linarith
  have hb' : psiDeficit (z - 1) + primePart (z - 1) ≤ b := by linarith
  have hpa := mul_le_mul_of_nonneg_left ha' (mul_nonneg hk0 hF)
  have hpb := mul_le_mul_of_nonneg_left hb' hH
  have hpair := actual_pair rh hN hI hk0 (by linarith : 25 ≤ z)
  have hpt := mul_le_mul_of_nonneg_left hpair hT
  have hidentity := linear_identity (k := k) hz0.ne' (by linarith : z ≠ 1)
  unfold margin
  nlinarith only [hactual', hkwc, hsqQ, hpa, hpb, hpt, hidentity]

noncomputable def numericMargin (k a b z : ℝ) : ℝ :=
  fullBase z + 1 / 1600 + k * F z * a - H z * b - (q z)^2 * Q z - T z * budget k z

theorem numericMargin_eq {k a b z : ℝ} (hz : z ≠ 0) :
    numericMargin k a b z = margin k a b z := by
  unfold numericMargin margin
  rw [SharpBase.sharpBase_eq_full hz]

#print axioms actual_pair
#print axioms actual_margin
#print axioms numericMargin_eq
end RHOcticPush.SpectralRam
