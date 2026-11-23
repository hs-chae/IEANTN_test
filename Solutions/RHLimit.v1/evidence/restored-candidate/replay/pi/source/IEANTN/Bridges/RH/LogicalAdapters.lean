/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Nodes.RHAdapters.v1.Conclusions
import IEANTN.Nodes.OpenAIQRH.v1.Conclusions
import IEANTN.Nodes.PlattTrudgian.v1.Conclusions
import Mathlib.Tactic

/-! Logical adapters only. No analytic estimate, zero count or numerical sum is proved here. -/
namespace RH.LogicalAdapters

/-- Positive real part excludes every negative-even trivial zero. -/
theorem nontrivial_of_pos_re {s : ℂ} (hs : 0 < s.re) :
    ¬ ∃ n : ℕ, s = -2 * (n + 1) := by
  rintro ⟨n, hn⟩
  have hre := congrArg Complex.re hn
  norm_num at hre
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

/-- The node's hypothesis has exactly the pinned Mathlib type. -/
theorem hypothesis_iff_mathlib : RH.v1.hypothesis ↔ RiemannHypothesis := Iff.rfl

/-- A zero to the right of 1/2 is nontrivial and contradicts RH. -/
theorem half_plane (hRH : RH.v1.hypothesis) {β : ℝ} (hβ : (1 / 2 : ℝ) ≤ β) :
    IEANTN.ZetaZeroFreeHalfPlane β := by
  intro s hs hs1 hz
  have hs0 : 0 < s.re := by linarith
  have hre := hRH s hz (nontrivial_of_pos_re hs0) hs1
  linarith

/-- RH supplies every finite-height RH rectangle in the actual project vocabulary. -/
theorem finite_height (hRH : RH.v1.hypothesis) (T : ℝ) :
    IEANTN.RiemannHypothesisUpTo T := by
  refine ⟨?_⟩
  rintro ⟨s, hs⟩
  rcases hs with ⟨hsre, hsim, hz⟩
  have hs0 : 0 < s.re := by linarith [hsre.1]
  have hs1 : s ≠ 1 := by
    intro heq
    subst s
    norm_num at hsre
  have hre := hRH s hz (nontrivial_of_pos_re hs0) hs1
  linarith [hsre.1]

/-- Conditional proof of the node's reusable half-plane conclusion. -/
theorem half_planes (hRH : RH.v1.hypothesis) : RHAdapters.v1.half_planes :=
  fun _ hβ => half_plane hRH hβ

/-- Conditional proof of the node's reusable finite-height conclusion. -/
theorem finite_heights (hRH : RH.v1.hypothesis) : RHAdapters.v1.finite_heights :=
  finite_height hRH

/-- Exact alias consumed by the existing QRH route. -/
theorem qrh (hRH : RH.v1.hypothesis) : OpenAIQRH.v1.zeta_seven_eighths :=
  half_plane hRH (by norm_num)

/-- Exact rounded Platt--Trudgian alias; no numerical verification is inferred. -/
theorem platt_trudgian (hRH : RH.v1.hypothesis) : PlattTrudgian.v1.rh_up_to :=
  finite_height hRH _

/-- Exact unrounded Platt--Trudgian alias; no zero count is inferred. -/
theorem platt_trudgian_exact (hRH : RH.v1.hypothesis) :
    PlattTrudgian.v1.rh_up_to_exact := finite_height hRH _

/-- A consumer that needs only finite-height RH can retain all its other inputs unchanged. -/
theorem apply_finite_height {P : Prop} (hRH : RH.v1.hypothesis) (T : ℝ)
    (consumer : IEANTN.RiemannHypothesisUpTo T → P) : P :=
  consumer (finite_height hRH T)

end RH.LogicalAdapters
