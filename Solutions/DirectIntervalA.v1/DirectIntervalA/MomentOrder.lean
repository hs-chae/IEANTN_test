/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import DirectIntervalA.Common
import DensityHeight

open Real Set MeasureTheory
namespace DirectIntervalA

 theorem moment_antitone {H : ℝ} (hH : 1 ≤ H) (hl : 1 ≤ log H) :
    AntitoneOn (fun s ↦ moment s H) (Icc (3/4 : ℝ) (7/8 : ℝ)) := by
  intro s hs t ht hst
  have h := CH2QRH.densityMomentMain_antitone hH hl hs ht hst
  unfold moment
  linarith

 theorem moment_nonneg {s H : ℝ} (hH : 1 < H) (hs : (3/4 : ℝ) ≤ s)
    (hs' : s ≤ 7/8) : 0 ≤ moment s H := by
  have hb : 0 < 1 - 8 * (1 - s) / 3 := by linarith
  have hlog : 0 < log H := log_pos hH
  have hq : 0 ≤ 5 - 2*s - 3 := by linarith
  have hH0 : 0 < H := by linarith
  have hq0 : 0 ≤ 5 - 2*s := by linarith
  have hq1 : 0 ≤ 5 - 2*s - 1 := by linarith
  have hq2 : 0 ≤ 5 - 2*s - 2 := by linarith
  unfold moment CH2QRH.densityMomentMain
  dsimp only
  positivity

 theorem moment_continuousOn {H : ℝ} (hH : 1 < H) :
    ContinuousOn (fun s ↦ moment s H) (Icc (3/4 : ℝ) (7/8 : ℝ)) := by
  intro s hs
  have hH0 : 0 < H := by linarith
  have hlog : 0 < log H := log_pos hH
  have hb : 0 < 1 - 8 * (1 - s) / 3 := by linarith [hs.1]
  have hb0 : 1 - 8 * (1 - s) / 3 ≠ 0 := hb.ne'
  have hbu : (1 - 8 * (1 - s) / 3) * log H ≠ 0 := mul_ne_zero hb0 hlog.ne'
  unfold moment CH2QRH.densityMomentMain
  dsimp only
  fun_prop (disch := first | assumption | positivity)

end DirectIntervalA
#print axioms DirectIntervalA.moment_antitone
#print axioms DirectIntervalA.moment_nonneg
#print axioms DirectIntervalA.moment_continuousOn
