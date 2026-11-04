/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import WinnerDensityA
namespace WinnerDensityA
/-- Strongest current complete-ray endpoint. All newly constructed source-to-program
and direct-prime bridges are proved; independent original analytic inputs remain explicit.
The native-assisted status is local and does not issue an official IEANTN receipt. -/
theorem winner_program_v2_height
    (hchj : WinnerDirectKernel.OriginalCHJSource)
    (hrvm : ZeroCount.v1.rvm_error_bound)
    (hrvmsmall : ZeroCount.v1.rvm_error_small)
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    (hs : WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH : IEANTN.RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hqrh : IEANTN.ZetaZeroFreeHalfPlane (7/8)) :
    IEANTN.HasPowerLogBound IEANTN.Eπ (2371/250000) 0 (7/8) (Real.exp 300) :=
  WinnerDensityA.HeightFinal.source_pi_009484 hchj hrvm hrvmsmall hlow hs hRH hqrh
#print axioms winner_program_v2_height
/-- Public conditional endpoint; source assumptions are independently named.
Local native-assisted evidence is separate from official IEANTN receipts. -/
theorem winner_program_v2 (hs : CH2Source) (h : WinnerPrimaryRectangle.HPYInputs)
    (hRH : IEANTN.RiemannHypothesisUpTo H)
    (hqrh : IEANTN.ZetaZeroFreeHalfPlane (7/8)) :
    IEANTN.HasPowerLogBound IEANTN.Eπ 0.009898 0 (7/8) (Real.exp 300) :=
  WinnerPrimaryRectangle.primary_tight_pi300 hs h hRH hqrh
/-- Same transfer and evaluator, updated Revers primary critical-line input. -/
theorem winner_program_v2_revers (hs : CH2Source) (h : WinnerPrimaryRectangle.ReversInputs)
    (hRH : IEANTN.RiemannHypothesisUpTo H)
    (hqrh : IEANTN.ZetaZeroFreeHalfPlane (7/8)) :
    IEANTN.HasPowerLogBound IEANTN.Eπ 0.009830 0 (7/8) (Real.exp 300) :=
  WinnerPrimaryRectangle.primary_revers_pi300 hs h hRH hqrh
#print axioms winner_program_v2_revers
#print axioms winner_program_v2
end WinnerDensityA
