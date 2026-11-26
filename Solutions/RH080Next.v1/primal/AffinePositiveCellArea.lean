/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import AffineCellInterpolation
import AffinePopulationBounds
import IEANTN.Vocabulary.CMSFunctional
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
set_option autoImplicit false
noncomputable section
open Real Set MeasureTheory
namespace RH080Next.Primal
open RH080Next.Explicit

def chord (a b t : ℝ) : ℝ := (1-t)*a+t*b
/-- Exact area of the positive part of a unit-cell affine segment. -/
def positiveChordArea (a b : ℝ) : ℝ :=
  if 0≤a then (if 0≤b then (a+b)/2 else a^2/(2*(a-b)))
  else (if 0≤b then b^2/(2*(b-a)) else 0)

private theorem integral_chord (a b l r : ℝ) (hlr : l≤r) :
    (∫ t in l..r, chord a b t)=a*(r-l)+(b-a)*(r^2-l^2)/2 := by
  have hd (t : ℝ) : HasDerivAt (fun z : ℝ => a*z+(b-a)*z^2/2) (chord a b t) t := by
    convert! ((hasDerivAt_id t).const_mul a).add
      (((hasDerivAt_id t).pow 2).const_mul (b-a) |>.div_const 2) using 1
    dsimp [chord]
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hlr
    (by fun_prop) (fun t ht => hd t)
    ((by unfold chord; fun_prop : Continuous (chord a b)).intervalIntegrable l r)]
  ring

theorem integral_positive_chord_of_nonneg {a b : ℝ} (ha : 0≤a) (hb : 0≤b) :
    (∫ t in (0:ℝ)..1, max 0 (chord a b t))=(a+b)/2 := by
  have he : (∫ t in (0:ℝ)..1, max 0 (chord a b t))=
      ∫ t in (0:ℝ)..1, chord a b t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by norm_num : (0:ℝ)≤1)] at ht
    apply max_eq_right
    dsimp [chord]
    exact add_nonneg (mul_nonneg (by linarith [ht.2]) ha) (mul_nonneg ht.1 hb)
  rw [he,integral_chord a b 0 1 (by norm_num)]
  ring

theorem integral_positive_chord_of_nonpos {a b : ℝ} (ha : a≤0) (hb : b≤0) :
    (∫ t in (0:ℝ)..1, max 0 (chord a b t))=0 := by
  have he : (∫ t in (0:ℝ)..1, max 0 (chord a b t))=
      ∫ t in (0:ℝ)..1, (0:ℝ) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by norm_num : (0:ℝ)≤1)] at ht
    apply max_eq_left
    dsimp [chord]
    exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos (by linarith [ht.2]) ha)
      (mul_nonpos_of_nonneg_of_nonpos ht.1 hb)
  rw [he]
  simp

theorem integral_positive_chord_downcross {a b : ℝ} (ha : 0≤a) (hb : b<0) :
    (∫ t in (0:ℝ)..1, max 0 (chord a b t))=a^2/(2*(a-b)) := by
  have hD : 0<a-b := by linarith
  let r : ℝ := a/(a-b)
  have hr0 : 0≤r := div_nonneg ha hD.le
  have hr1 : r≤1 := (div_le_one hD).2 (by linarith)
  have hc : Continuous (fun t : ℝ => max 0 (chord a b t)) := by unfold chord; fun_prop
  have hL : (∫ t in (0:ℝ)..r, max 0 (chord a b t))=
      ∫ t in (0:ℝ)..r, chord a b t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hr0] at ht
    apply max_eq_right
    have h := (le_div_iff₀ hD).mp ht.2
    dsimp [chord]
    nlinarith
  have hR : (∫ t in r..1, max 0 (chord a b t))=0 := by
    have he : (∫ t in r..1, max 0 (chord a b t))=∫ t in r..1, (0:ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hr1] at ht
      apply max_eq_left
      have h := (div_le_iff₀ hD).mp ht.1
      dsimp [chord]
      nlinarith
    rw [he]; simp
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable 0 r)
    (hc.intervalIntegrable r 1),hL,hR,add_zero,integral_chord a b 0 r hr0]
  dsimp [r]
  field_simp
  <;> ring

theorem integral_positive_chord_upcross {a b : ℝ} (ha : a<0) (hb : 0≤b) :
    (∫ t in (0:ℝ)..1, max 0 (chord a b t))=b^2/(2*(b-a)) := by
  have hD : 0<b-a := by linarith
  let r : ℝ := -a/(b-a)
  have hr0 : 0≤r := div_nonneg (by linarith) hD.le
  have hr1 : r≤1 := (div_le_one hD).2 (by linarith)
  have hc : Continuous (fun t : ℝ => max 0 (chord a b t)) := by unfold chord; fun_prop
  have hL : (∫ t in (0:ℝ)..r, max 0 (chord a b t))=0 := by
    have he : (∫ t in (0:ℝ)..r, max 0 (chord a b t))=∫ t in (0:ℝ)..r, (0:ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hr0] at ht
      apply max_eq_left
      have h := (le_div_iff₀ hD).mp ht.2
      dsimp [chord]
      nlinarith
    rw [he]; simp
  have hR : (∫ t in r..1, max 0 (chord a b t))=∫ t in r..1, chord a b t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hr1] at ht
    apply max_eq_right
    have h := (div_le_iff₀ hD).mp ht.1
    dsimp [chord]
    nlinarith
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable 0 r)
    (hc.intervalIntegrable r 1),hL,hR,zero_add,integral_chord a b r 1 hr1]
  dsimp [r]
  field_simp
  <;> ring

/-- Complete exact positive-cell area theorem, including every zero endpoint. -/
theorem integral_positive_chord (a b : ℝ) :
    (∫ t in (0:ℝ)..1, max 0 (chord a b t))=positiveChordArea a b := by
  unfold positiveChordArea
  split_ifs with ha hb hb
  · exact integral_positive_chord_of_nonneg ha hb
  · exact integral_positive_chord_downcross ha (lt_of_not_ge hb)
  · exact integral_positive_chord_upcross (lt_of_not_ge ha) hb
  · exact integral_positive_chord_of_nonpos (le_of_not_ge ha) (le_of_not_ge hb)

/-- Exact physical-cell area of the positive part of the genuine spectrum. -/
theorem integral_positive_affine_cell (nodes : List ℚ) (m : ℕ)
    (hlen : 2≤nodes.length) (hm : 0<m) (hlast : node nodes (nodes.length-1)=0)
    (j : ℕ) (hj : j<nodes.length-1) :
    (∫ v in (j:ℝ)/(m:ℝ)..((j+1:ℕ):ℝ)/(m:ℝ),
      max 0 (affineSpectrum nodes m v))=
      positiveChordArea (node nodes j) (node nodes (j+1))/(m:ℝ) := by
  have hm' : (0:ℝ)<m := by exact_mod_cast hm
  have hm0 := hm'.ne'
  have hphase (t : ℝ) (ht : t∈Icc (0:ℝ) 1) :
      affineSpectrum nodes m ((1/(m:ℝ))*t+(j:ℝ)/(m:ℝ))=
        chord (node nodes j) (node nodes (j+1)) t := by
    have hv : (m:ℝ)*((1/(m:ℝ))*t+(j:ℝ)/(m:ℝ))=t+j := by field_simp
    rw [affineSpectrum_cell_phase nodes m hlen hlast j hj _
      (by rw [hv]; linarith [ht.1]) (by rw [hv]; linarith [ht.2]),hv]
    unfold chord
    ring
  have hi : (∫ t in (0:ℝ)..1,
      max 0 (affineSpectrum nodes m ((1/(m:ℝ))*t+(j:ℝ)/(m:ℝ))))=
      positiveChordArea (node nodes j) (node nodes (j+1)) := by
    rw [← integral_positive_chord]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by norm_num : (0:ℝ)≤1)] at ht
    change max 0 (affineSpectrum nodes m ((1/(m:ℝ))*t+(j:ℝ)/(m:ℝ))) = _
    rw [hphase t ht]
  have hsub := intervalIntegral.smul_integral_comp_mul_add
    (fun v : ℝ => max 0 (affineSpectrum nodes m v)) (a := 0) (b := 1)
    (1/(m:ℝ)) ((j:ℝ)/(m:ℝ))
  simp only [smul_eq_mul,mul_zero,zero_add,mul_one] at hsub
  rw [show 1/(m:ℝ)+(j:ℝ)/(m:ℝ)=((j+1:ℕ):ℝ)/(m:ℝ) by push_cast; ring] at hsub
  rw [← hsub,hi]
  ring

/-- The positive spectrum really is integrable; the following identities do not
use a totalized integral of a nonintegrable function. -/
theorem integrable_positive_affineSpectrum (nodes : List ℚ) (m : ℕ)
    (hlen : 2≤nodes.length) (hm : 0<m) :
    Integrable (fun v : ℝ => max 0 (affineSpectrum nodes m v)) := by
  have hi := integrable_affineSpectrum nodes m hlen hm
  have he : (fun v : ℝ => max 0 (affineSpectrum nodes m v))=
      fun v : ℝ => (|affineSpectrum nodes m v|+affineSpectrum nodes m v)/2 := by
    funext v
    rcases le_total 0 (affineSpectrum nodes m v) with h | h
    · rw [max_eq_right h,abs_of_nonneg h]; ring
    · rw [max_eq_left h,abs_of_nonpos h]; ring
  rw [he]
  exact (hi.abs.add hi).div_const 2

private theorem integral_positive_right_support (nodes : List ℚ) (m : ℕ)
    (hlen : 2≤nodes.length) (hm : 0<m) (hmN : m≤nodes.length-1) :
    (∫ v in Ioi (1:ℝ), max 0 (affineSpectrum nodes m v))=
      ∫ v in (1:ℝ)..radius nodes m, max 0 (affineSpectrum nodes m v) := by
  have hm' : (0:ℝ)<m := by exact_mod_cast hm
  have hR : (1:ℝ)≤radius nodes m := by
    unfold radius
    apply (le_div_iff₀ hm').2
    simpa using (show (m:ℝ)≤((nodes.length-1:ℕ):ℝ) by exact_mod_cast hmN)
  rw [intervalIntegral.integral_of_le hR,← integral_indicator measurableSet_Ioi,
    ← integral_indicator measurableSet_Ioc]
  apply congrArg (fun f : ℝ → ℝ => ∫ v : ℝ, f v)
  funext v
  by_cases hv1 : 1<v
  · by_cases hvR : v≤radius nodes m
    · simp [Set.indicator,hv1,hvR]
    · have hzero := affineSpectrum_eq_zero_of_radius_le nodes m hlen hm v
        ((le_of_not_ge hvR).trans (le_abs_self v))
      simp [Set.indicator,hv1,hvR,hzero]
  · simp [Set.indicator,hv1]

def nodalPositiveArea (nodes : List ℚ) (m : ℕ) : ℝ :=
  (2/(m:ℝ))*∑ j ∈ Finset.Ico m (nodes.length-1),
    positiveChordArea (node nodes j) (node nodes (j+1))

/-- Exact full exterior positive leakage of every supported affine spectrum.
No sampled positive-part values or numerical leakage premise are substituted. -/
theorem positiveLeak_affineSpectrum_eq_nodalPositiveArea (nodes : List ℚ) (m : ℕ)
    (hlen : 2≤nodes.length) (hm : 0<m) (hmN : m≤nodes.length-1)
    (hlast : node nodes (nodes.length-1)=0) :
    IEANTN.CMSFunctional.positiveLeak (affineSpectrum nodes m)=nodalPositiveArea nodes m := by
  have hm' : (0:ℝ)<m := by exact_mod_cast hm
  have hc : Continuous (fun v : ℝ => max 0 (affineSpectrum nodes m v)) := by
    exact continuous_const.max (continuous_affineSpectrum nodes m)
  have hs := intervalIntegral.sum_integral_adjacent_intervals_Ico (μ := volume)
    (f := fun v : ℝ => max 0 (affineSpectrum nodes m v))
    (a := fun j : ℕ => (j:ℝ)/(m:ℝ)) hmN
    (fun j hj => hc.intervalIntegrable _ _)
  have hcells : (∑ j ∈ Finset.Ico m (nodes.length-1),
      ∫ v in (j:ℝ)/(m:ℝ)..((j+1:ℕ):ℝ)/(m:ℝ),max 0 (affineSpectrum nodes m v))=
      ∑ j ∈ Finset.Ico m (nodes.length-1),
        positiveChordArea (node nodes j) (node nodes (j+1))/(m:ℝ) := by
    apply Finset.sum_congr rfl
    intro j hj
    exact integral_positive_affine_cell nodes m hlen hm hlast j (Finset.mem_Ico.mp hj).2
  rw [hs,div_self hm'.ne'] at hcells
  unfold IEANTN.CMSFunctional.positiveLeak IEANTN.CMSFunctional.exterior
  rw [exterior_positive_integral_even _ (affineSpectrum_even nodes m),
    integral_positive_right_support nodes m hlen hm hmN]
  change 2*(∫ v in (1:ℝ)..((nodes.length-1:ℕ):ℝ)/(m:ℝ),
    max 0 (affineSpectrum nodes m v))=nodalPositiveArea nodes m
  rw [hcells,← Finset.sum_div]
  unfold nodalPositiveArea
  ring

#print axioms integral_positive_chord
#print axioms integral_positive_affine_cell
#print axioms integrable_positive_affineSpectrum
#print axioms positiveLeak_affineSpectrum_eq_nodalPositiveArea
end RH080Next.Primal
