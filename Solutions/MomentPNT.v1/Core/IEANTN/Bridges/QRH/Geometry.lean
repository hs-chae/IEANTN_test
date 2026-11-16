/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Vocabulary.ZeroFreeHalfPlane
import IEANTN.Vocabulary.Zeta
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic

/-! Reusable geometric consequences of an open zero-free half-plane. -/

namespace QRHGeometry
open Real IEANTN

/-- A genuine empty zero set, not an appeal to the default value of an infinite sum. -/
theorem density_vanishes {β σ T : ℝ} (hβ : ZetaZeroFreeHalfPlane β) (hσ : β ≤ σ) :
    zetaN' σ T = 0 := by
  classical
  have he : IsEmpty (zetaZeroesIn (Set.Ioo σ 1) (Set.Ioo 0 T)) := ⟨fun z ↦ by
    have hz := z.property
    have hn : (z : ℂ) ≠ 1 := by
      intro h
      have hlt := hz.1.2
      simp only [h, Complex.one_re] at hlt
      exact (lt_irrefl 1) hlt
    exact hβ z (lt_of_le_of_lt hσ hz.1.1) hn hz.2.2⟩
  letI := he
  simp [zetaN', zetaZeroesSum]

/-- The strict inequality protects the closed boundary of the target region. -/
theorem classical_region {β R t₀ : ℝ} (hβlt : β < 1) (hR : 0 < R) (ht₀ : 1 < t₀)
    (hcut : 1 / (R * (1 - β)) < log t₀) (hβ : ZetaZeroFreeHalfPlane β) :
    ClassicalZeroFreeRegion R t₀ := by
  intro σ t htt hσ
  have ht : 1 < t := lt_of_lt_of_le ht₀ htt
  have hlog : 0 < log t := log_pos ht
  have hlt : 1 / (R * (1 - β)) < log t :=
    hcut.trans_le (log_le_log (by linarith) htt)
  have hmul : 1 < log t * (R * (1 - β)) :=
    (div_lt_iff₀ (mul_pos hR (sub_pos.mpr hβlt))).mp hlt
  have hdiv : 1 / (R * log t) < 1 - β :=
    (div_lt_iff₀ (mul_pos hR hlog)).mpr (by nlinarith [hmul])
  apply hβ (σ + t * Complex.I)
  · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    linarith
  · intro he
    have him := congrArg Complex.im he
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add, Complex.one_im] at him
    linarith

/-- Reciprocal zeta is holomorphic on the asserted half-plane away from the pole. -/
theorem reciprocal_differentiable {β : ℝ} (hβ : ZetaZeroFreeHalfPlane β) :
    DifferentiableOn ℂ (fun s : ℂ ↦ (riemannZeta s)⁻¹) {s | β < s.re ∧ s ≠ 1} := by
  intro s hs
  exact ((differentiableAt_riemannZeta hs.2).inv (hβ s hs.1 hs.2)).differentiableWithinAt

end QRHGeometry
