/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Vocabulary.RHSmoothing
import LeanCert.Tactic.IntervalAuto

/-! A genuine active point of the checked PNT source frontier, not a sampled
whole-ray claim. Every numerical inequality here is ordinary Lean kernel
interval verification, not source-first PV. The moment/analytic provider
premises of the actual psi conclusion remain separately required. -/
namespace RHContinuation.FrontierPoint
open Real
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option leancert.trust "kernel"

noncomputable def leeNosal1 (L : ℝ) : ℝ :=
  L ^ 2 / (8 * Real.pi) - (L / (2 * Real.pi) + 1465 / 1000) * log L + 12325 / 10000 * L
noncomputable def leeNosal2 (L : ℝ) : ℝ := L * (L - log L) / (8 * Real.pi)
noncomputable def ch94 (L : ℝ) : ℝ :=
  ((L - 2 * log (L / (Real.pi * exp 1))) ^ 2 - 4) / (8 * Real.pi)

theorem box_at_100 : IEANTN.RHSmoothing.fastBound 100 < 355 := by
  unfold IEANTN.RHSmoothing.fastBound IEANTN.RHSmoothing.envelope IEANTN.RHSmoothing.v
  interval_decide 80 (trust := kernel) <;> norm_num [LeanCert.Core.MathConst.toReal] <;> ring

theorem B5_at_100 : (355 : ℝ) < IEANTN.RHSmoothing.envelope (831/1000) (287/500) 100 := by
  unfold IEANTN.RHSmoothing.envelope IEANTN.RHSmoothing.v
  interval_decide 80 (trust := kernel) <;> norm_num [LeanCert.Core.MathConst.toReal] <;> ring

theorem leeNosal1_at_100 : (355 : ℝ) < leeNosal1 100 := by
  unfold leeNosal1
  interval_decide 80 (trust := kernel) <;> norm_num [LeanCert.Core.MathConst.toReal] <;> ring

theorem leeNosal2_at_100 : (355 : ℝ) < leeNosal2 100 := by
  unfold leeNosal2
  interval_decide 80 (trust := kernel) <;> norm_num [LeanCert.Core.MathConst.toReal] <;> ring

theorem ch94_at_100 : (355 : ℝ) < ch94 100 := by
  unfold ch94
  interval_decide 80 (trust := kernel) <;> norm_num [LeanCert.Core.MathConst.toReal] <;> ring

theorem schoenfeld_at_100 : (355 : ℝ) < 100 ^ 2 / (8 * Real.pi) := by
  interval_decide 80 (trust := kernel) <;> norm_num [LeanCert.Core.MathConst.toReal] <;> ring

theorem recovered_CH_at_100 : (355 : ℝ) < IEANTN.RHSmoothing.chBound 100 := by
  unfold IEANTN.RHSmoothing.chBound
  interval_decide 80 (trust := kernel) <;> norm_num [LeanCert.Core.MathConst.toReal] <;> ring

theorem outside_Buthe_finite : (1024/1000:ℝ) * 10^19 < exp 100 := by
  interval_decide 80 (trust := kernel) <;> norm_num [LeanCert.Core.MathConst.toReal] <;> ring

#print axioms box_at_100
#print axioms B5_at_100
#print axioms leeNosal1_at_100
#print axioms leeNosal2_at_100
#print axioms ch94_at_100
#print axioms schoenfeld_at_100
#print axioms recovered_CH_at_100
#print axioms outside_Buthe_finite
end RHContinuation.FrontierPoint
