/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import NicolasBaseline
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace RHLimit.NicolasMass
open Real Complex Filter Set
open scoped Topology
set_option maxHeartbeats 0
set_option maxRecDepth 100000

abbrev Zero := NicolasContinuation.Zero

noncomputable def coefficient (z : Zero) : ℂ :=
  (NicolasContinuation.multiplicity z : ℂ) / (z.val * (1-z.val))
noncomputable def weight (z : Zero) : ℝ :=
  (NicolasContinuation.multiplicity z : ℝ) / ‖z.val‖^2
noncomputable def phaseTerm (x : ℝ) (z : Zero) : ℂ :=
  coefficient z * Complex.exp (Complex.I * (z.val.im : ℂ) * (Real.log x : ℂ))

lemma zero_re (hRH : RiemannHypothesis) (z : Zero) : z.val.re = 1/2 := by
  apply hRH z.val z.property.2.2
  · rintro ⟨n, hn⟩
    have hr := congrArg Complex.re hn
    norm_num at hr
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith [z.property.1]
  · intro hn
    have hr := congrArg Complex.re hn
    norm_num at hr
    linarith [z.property.2.1]

lemma one_sub_eq_conj (hRH : RiemannHypothesis) (z : Zero) :
    1-z.val = (starRingEnd ℂ) z.val := by
  have hr := zero_re hRH z
  apply Complex.ext <;> norm_num [Complex.sub_re, Complex.sub_im, hr]

lemma coefficient_ofReal (hRH : RiemannHypothesis) (z : Zero) :
    coefficient z = (weight z : ℂ) := by
  have hd : z.val * (1-z.val) = (‖z.val‖^2 : ℂ) := by
    rw [one_sub_eq_conj hRH z, Complex.mul_conj']
  simp only [coefficient, weight, hd, Complex.ofReal_div, Complex.ofReal_natCast,
    Complex.ofReal_pow]

lemma weight_nonneg (z : Zero) : 0 ≤ weight z := by unfold weight; positivity

lemma phase_norm (hRH : RiemannHypothesis) (x : ℝ) (z : Zero) :
    ‖phaseTerm x z‖ = weight z := by
  unfold phaseTerm
  rw [norm_mul, coefficient_ofReal hRH z, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (weight_nonneg z), Complex.norm_exp]
  simp

lemma source_term_eq_phase {x : ℝ} (hx : 0 < x) (z : Zero) :
    NicolasContinuation.spectralTerm x z = phaseTerm x z := by
  unfold NicolasContinuation.spectralTerm phaseTerm coefficient
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'), ← Complex.ofReal_log hx.le]
  have he : (Real.log x : ℂ) * (Complex.I * (z.val.im : ℂ)) =
      Complex.I * (z.val.im : ℂ) * (Real.log x : ℂ) := by ring
  rw [he]
  ring

/-- The existing full Nicolas source already supplies absolute summability.
Only one legal source argument, x=2, is needed for this step. -/
theorem weight_summable (hRH : RiemannHypothesis)
    (hN : NicolasContinuation.SourceNicolas119) : Summable weight := by
  have hs := (hN hRH 2 (by norm_num)).1.norm
  apply hs.congr
  intro z
  rw [source_term_eq_phase (by norm_num : (0 : ℝ) < 2)]
  exact phase_norm hRH 2 z

lemma phase_sum_continuous (hRH : RiemannHypothesis)
    (hs : Summable weight) :
    ContinuousOn (fun x : ℝ => ∑' z : Zero, phaseTerm x z) (Ioi 0) := by
  apply continuousOn_tsum (u := weight)
  · intro z x hx
    have hlog : ContinuousAt (fun t : ℝ => (Real.log t : ℂ)) x :=
      Complex.continuous_ofReal.continuousAt.comp (Real.continuousAt_log hx.ne')
    have he : ContinuousAt
        (fun t : ℝ => Complex.exp (Complex.I * (z.val.im : ℂ) * (Real.log t : ℂ))) x :=
      Complex.continuous_exp.continuousAt.comp (continuousAt_const.mul hlog)
    exact (continuousAt_const.mul he).continuousWithinAt
  · exact hs
  · intro z x _
    exact (phase_norm hRH x z).le

lemma phase_sum_one (hRH : RiemannHypothesis) :
    (∑' z : Zero, phaseTerm 1 z).re = ∑' z : Zero, weight z := by
  have he : (∑' z : Zero, phaseTerm 1 z) = ∑' z : Zero, (weight z : ℂ) := by
    apply tsum_congr
    intro z
    simp [phaseTerm, coefficient_ofReal hRH z]
  rw [he, ← Complex.ofReal_tsum]
  simp

/-- Recover the positive inverse-square mass at x=1 by an actual right limit.
The cited source is only used on its stated open domain x>1. -/
theorem mass_le_beta (hRH : RiemannHypothesis)
    (hN : NicolasContinuation.SourceNicolas119) :
    (∑' z : Zero, weight z) ≤ NicolasContinuation.beta := by
  have hs := weight_summable hRH hN
  have hc := phase_sum_continuous hRH hs
  have hc1 : ContinuousAt (fun x : ℝ => ∑' z : Zero, phaseTerm x z) 1 :=
    hc.continuousAt (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have ht : Tendsto (fun x : ℝ => (∑' z : Zero, phaseTerm x z).re)
      (𝓝[>] (1 : ℝ)) (𝓝 (∑' z : Zero, weight z)) := by
    have h : Tendsto (fun x : ℝ => (∑' z : Zero, phaseTerm x z).re)
        (𝓝[>] (1 : ℝ)) (𝓝 ((∑' z : Zero, phaseTerm 1 z).re)) :=
      (Complex.continuous_re.continuousAt.comp hc1).tendsto.mono_left nhdsWithin_le_nhds
    simpa only [phase_sum_one hRH] using h
  apply le_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx1 : 1 < x := hx
  have he : NicolasContinuation.W x = (∑' z : Zero, phaseTerm x z).re := by
    unfold NicolasContinuation.W
    congr 1
    exact tsum_congr (source_term_eq_phase (by linarith : (0 : ℝ) < x))
  rw [← he]
  exact (le_abs_self _).trans (hN hRH x hx1).2

#print axioms mass_le_beta
#print axioms weight_summable
end RHLimit.NicolasMass
