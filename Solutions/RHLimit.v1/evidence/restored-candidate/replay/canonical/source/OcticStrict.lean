/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import OcticTwoInputs

namespace RHLimit.OcticStrict
open Real Set
open RHLimit.OcticGeometry RHLimit.OcticPrimePowers
set_option maxHeartbeats 2000000

/-- The exact generic argument retains the actual strict open-window count. -/
theorem open_count_from_kernel (n : ℕ) (C A B R P T η : ℝ)
    (rh : RiemannHypothesis) (hef : EvenKernel.ExplicitFormula n C)
    (hz : EvenKernel.ZeroEstimate n C A B R) (hpp : EvenKernel.PrimePowerCost n C P)
    (ht : EvenKernel.TrivialCost n C T)
    (hg : EvenKernel.ScalarGeometry n C A B R P T η)
    (hc : EvenKernel.ForwardCoverage C) :
    ∀ u : ℝ, exp 24 ≤ u →
      (EvenKernel.countCoefficient n A C + η / log u) * sqrt u <
        ((QuarticWindow.primesBetween u (u + C * sqrt u * log u)).card : ℝ) := by
  intro u hu
  obtain ⟨L, hL, hcenter, hwidth⟩ := hc u hu
  obtain ⟨ha, hla, hab, hlog, hδ, hd, hlam, hη, hmargin⟩ := hg L hL
  have heq := (hef rh L hL).2
  have hz' := (le_abs_self (EvenKernel.zeroTerm n C L).re).trans
    ((Complex.abs_re_le_norm _).trans (hz rh L hL))
  have hm := EvenKernel.mainTerm_lower n hd
  have hp := hpp L hL
  have ht' := ht L hL
  have hpop : EvenKernel.countCoefficient n A C * L + η < EvenKernel.population n C L := by
    unfold EvenKernel.D at hm
    unfold EvenKernel.countCoefficient
    nlinarith
  have hbound := EvenKernel.population_le_count n ha hla
  have hloga : 0 < log (EvenKernel.a C L) := by linarith
  have hsa : 0 < sqrt (EvenKernel.a C L) := Real.sqrt_pos.mpr ha
  have hstrict : EvenKernel.countCoefficient n A C * log (EvenKernel.a C L) + η <
      ((QuarticWindow.primesBetween (EvenKernel.a C L) (EvenKernel.b C L)).card : ℝ) *
        (log (EvenKernel.a C L) / sqrt (EvenKernel.a C L)) := by
    have hh : EvenKernel.countCoefficient n A C * log (EvenKernel.a C L) ≤
        EvenKernel.countCoefficient n A C * L :=
      mul_le_mul_of_nonneg_left (by linarith) hlam
    linarith
  have hdiv := (div_lt_iff₀ (div_pos hloga hsa)).mpr hstrict
  have hfield : (EvenKernel.countCoefficient n A C * log (EvenKernel.a C L) + η) /
      (log (EvenKernel.a C L) / sqrt (EvenKernel.a C L)) =
      (EvenKernel.countCoefficient n A C + η / log (EvenKernel.a C L)) *
        sqrt (EvenKernel.a C L) := by field_simp <;> ring
  rw [hfield, hcenter] at hdiv
  have hsub : QuarticWindow.primesBetween (EvenKernel.a C L) (EvenKernel.b C L) ⊆
      QuarticWindow.primesBetween u (u + C * sqrt u * log u) := by
    intro p hp
    have hmem := Finset.mem_filter.mp hp
    have hpprime := Nat.mem_primesLE.mp hmem.1
    apply Finset.mem_filter.mpr
    refine ⟨Nat.mem_primesLE.mpr ⟨hpprime.1.trans (Nat.floor_le_floor hwidth), hpprime.2⟩, ?_⟩
    rw [hcenter] at hmem
    exact ⟨hmem.2.1, hmem.2.2.trans_le hwidth⟩
  have hcard : ((QuarticWindow.primesBetween (EvenKernel.a C L)
      (EvenKernel.b C L)).card : ℝ) ≤
      ((QuarticWindow.primesBetween u (u + C * sqrt u * log u)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  rw [hcenter] at hcard
  exact hdiv.trans_le hcard

/-- The stated2.15 result with both interval endpoints strictly excluded. -/
theorem count_215 (rh : RiemannHypothesis)
    (hef : EvenKernel.ExplicitFormula 4 (43 / 20))
    (hz : EvenKernel.ZeroEstimate 4 (43 / 20) (911 / 500) (3 / 2) (3 / 125)) :
    ∀ u : ℝ, exp 24 ≤ u →
      (9001 / 9000 + (29 / 5) / log u) * sqrt u <
        ((QuarticWindow.primesBetween u (u + 43 / 20 * sqrt u * log u)).card : ℝ) := by
  have h := open_count_from_kernel 4 (43 / 20) (911 / 500) (3 / 2)
    (3 / 125) (31 / 2000) (1 / 1000) (29 / 5) rh hef hz primepower_cost_215
    trivial_cost_215 scalar_geometry_215 forward_coverage_215
  norm_num [EvenKernel.countCoefficient, EvenKernel.mass] at h ⊢
  exact h

/-- The full realC frontier with both interval endpoints strictly excluded. -/
theorem count_family (rh : RiemannHypothesis)
    (hef : ∀ C ∈ Set.Icc (103 / 100 : ℝ) 16, EvenKernel.ExplicitFormula 4 C)
    (hz : ∀ C ∈ Set.Icc (103 / 100 : ℝ) 16,
      EvenKernel.ZeroEstimate 4 C (911 / 500) (3 / 2) (3 / 20)) :
    ∀ C ∈ Set.Icc (103 / 100 : ℝ) 16, ∀ u : ℝ, exp 24 ≤ u →
      (8 / 9 * C - 911 / 1000 + (21 / 5) / log u) * sqrt u <
        ((QuarticWindow.primesBetween u (u + C * sqrt u * log u)).card : ℝ) := by
  intro C hC
  have h := open_count_from_kernel 4 C (911 / 500) (3 / 2) (3 / 20)
    (29 / 500) (1 / 1000) (21 / 5) rh (hef C hC) (hz C hC)
    (primepower_cost_family 4 hC) (trivial_cost_family 4 hC)
    (scalar_geometry_family hC) (forward_coverage_family hC)
  norm_num [EvenKernel.countCoefficient, EvenKernel.mass] at h
  convert h using 1 <;> ring

#print axioms count_215
#print axioms count_family
end RHLimit.OcticStrict
