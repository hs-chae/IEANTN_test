/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import WinnerDensityA.TightContext
import WinnerDensityA.TightAssembly
namespace WinnerDensityA
open Real IEANTN
/-- The new density input is derived, with every new numerical obligation
supplied by the concrete provider. Only independently named source facts remain. -/
theorem tight_density_input (h : WinnerSourceContext.OriginalInputs) (hRH : RiemannHypothesisUpTo H) :
    DensityInput (ModelProgram.modelC (151/20) (271/50)) (fun _ ↦ 6) := by
  intro sigma T hs hs' hT
  have ht : WinnerOriginalScalars.height≤T := by simpa [H,WinnerOriginalScalars.height] using hT
  have hb := WinnerSourceContext.actual_count_tight_from_original_sources h (by simpa [H,WinnerOriginalScalars.height] using hRH) hs hs' ht
  simpa only [ModelProgram.modelC,show -(271/50:ℝ)*(7/8-sigma)= (271/50:ℝ)*(sigma-7/8) by ring,poly] using hb

/-- Actual ψ bound from original sources, closed Gaussian computation and QRH. -/
theorem tight_source_psi300 (hs : CH2Source) (h : WinnerSourceContext.OriginalInputs)
    (hRH : RiemannHypothesisUpTo H) (hqrh : ZetaZeroFreeHalfPlane (7/8)) :
    HasPowerLogBound Eψ 0.009850 0 (7/8) (exp 300) :=
  Tight.psi300 hs (tight_density_input h hRH) hRH hqrh

/-- Actual θ bound, including the prime-power correction. -/
theorem tight_source_theta300 (hs : CH2Source) (h : WinnerSourceContext.OriginalInputs)
    (hRH : RiemannHypothesisUpTo H) (hqrh : ZetaZeroFreeHalfPlane (7/8)) :
    HasPowerLogBound Eθ (0.009850+1/10^12) 0 (7/8) (exp 300) :=
  Tight.theta300 hs (tight_density_input h hRH) hRH hqrh

/-- End-to-end source-linked prime-counting theorem. No new density, U,
Gaussian-tail, chosen numerical coefficient or prime bound is assumed. -/
theorem tight_source_pi300 (hs : CH2Source) (h : WinnerSourceContext.OriginalInputs)
    (hRH : RiemannHypothesisUpTo H) (hqrh : ZetaZeroFreeHalfPlane (7/8)) :
    HasPowerLogBound Eπ 0.009898 0 (7/8) (exp 300) :=
  Tight.pi300 hs (tight_density_input h hRH) hRH hqrh
#print axioms tight_density_input
#print axioms tight_source_pi300
end WinnerDensityA
