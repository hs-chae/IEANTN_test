/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import WinnerDensityA.ReversContext
import WinnerDensityA.ReversAssembly
namespace WinnerDensityA
open Real IEANTN
/-- The new density input is derived, with every new numerical obligation
supplied by the concrete provider. Only independently named source facts remain. -/
theorem revers_density_input (h : WinnerSourceContext.ReversInputs) (hRH : RiemannHypothesisUpTo H) :
    DensityInput (ModelProgram.modelC (15/2) (547/100)) (fun _ ↦ 6) := by
  intro sigma T hs hs' hT
  have ht : WinnerOriginalScalars.height≤T := by simpa [H,WinnerOriginalScalars.height] using hT
  have hb := WinnerSourceContext.actual_count_revers_from_original_sources h (by simpa [H,WinnerOriginalScalars.height] using hRH) hs hs' ht
  simpa only [ModelProgram.modelC,show -(547/100:ℝ)*(7/8-sigma)= (547/100:ℝ)*(sigma-7/8) by ring,poly] using hb

/-- Actual ψ bound from original sources, closed Gaussian computation and QRH. -/
theorem revers_source_psi300 (hs : CH2Source) (h : WinnerSourceContext.ReversInputs)
    (hRH : RiemannHypothesisUpTo H) (hqrh : ZetaZeroFreeHalfPlane (7/8)) :
    HasPowerLogBound Eψ 0.009782 0 (7/8) (exp 300) :=
  Revers.psi300 hs (revers_density_input h hRH) hRH hqrh

/-- Actual θ bound, including the prime-power correction. -/
theorem revers_source_theta300 (hs : CH2Source) (h : WinnerSourceContext.ReversInputs)
    (hRH : RiemannHypothesisUpTo H) (hqrh : ZetaZeroFreeHalfPlane (7/8)) :
    HasPowerLogBound Eθ (0.009782+1/10^12) 0 (7/8) (exp 300) :=
  Revers.theta300 hs (revers_density_input h hRH) hRH hqrh

/-- End-to-end source-linked prime-counting theorem. No new density, U,
Gaussian-tail, chosen numerical coefficient or prime bound is assumed. -/
theorem revers_source_pi300 (hs : CH2Source) (h : WinnerSourceContext.ReversInputs)
    (hRH : RiemannHypothesisUpTo H) (hqrh : ZetaZeroFreeHalfPlane (7/8)) :
    HasPowerLogBound Eπ 0.009830 0 (7/8) (exp 300) :=
  Revers.pi300 hs (revers_density_input h hRH) hRH hqrh
#print axioms revers_density_input
#print axioms revers_source_pi300
end WinnerDensityA
