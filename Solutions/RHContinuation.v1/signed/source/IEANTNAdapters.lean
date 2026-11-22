/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import SourceInterfaces
import IEANTN.Nodes.Buthe.v1.Conclusions
namespace MertensPositive

theorem buthe_psi_adapter (h : Buthe.v1.theorem_2_psi) : PublishedButhePsi := by
  intro x hx hM
  simpa only [abs_sub_comm] using h x hx hM

theorem buthe_theta_lower_adapter (h : Buthe.v1.theorem_2_theta) :
    PublishedButheThetaLower := by
  intro x hx hM
  linarith [h x hx hM]

theorem buthe_theta_upper_adapter (h : Buthe.v1.theorem_2_theta_lower) :
    PublishedButheThetaUpper := by
  intro x hx hM
  linarith [h x hx hM]

/-- Actual existing IEANTN source contracts discharge all three finite inputs. -/
theorem first_mertens_positive_IEANTN
    (h154 : SourceBFKNW154) (h21 : SourceBFKNW21)
    (hPsi : Buthe.v1.theorem_2_psi) (hThetaL : Buthe.v1.theorem_2_theta)
    (hThetaU : Buthe.v1.theorem_2_theta_lower) (hRH : RiemannHypothesis)
    {x : ℝ} (hx : Real.exp 24 ≤ x) (hxM : x ≤ (10:ℝ)^19) :
    0.006 / Real.sqrt x < A x - Real.log x - E :=
  first_mertens_positive_from_original_sources h154 h21
    (buthe_psi_adapter hPsi) (buthe_theta_lower_adapter hThetaL)
    (buthe_theta_upper_adapter hThetaU) hRH hx hxM

#print axioms first_mertens_positive_IEANTN
end MertensPositive
