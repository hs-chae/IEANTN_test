/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Nodes.ZeroCount.v1.Conclusions
namespace ZeroCountEnvelope.v1
open Real
noncomputable def bptAllowance (L:ℝ) : ℝ := (7/25:ℝ)*L
/-- BW first bound after adding7/8 for the actual center change. -/
noncomputable def bwFirstAllowance (L:ℝ) : ℝ :=
  (2519/25000:ℝ)*L+(1223/5000:ℝ)*log L+223961/25000
/-- BW second bound after adding7/8 for the actual center change. -/
noncomputable def bwSecondAllowance (L:ℝ) : ℝ :=
  (14/125:ℝ)*L+(12567/100000:ℝ)*log L+464917/100000
/-- Actual three-source zero-count envelope. Restricting BPT to non-ordinates
avoids silently choosing a convention at jumps; BW itself holds at all heights. -/
def off_ordinate_envelope : Prop := ∀ T:ℝ,2*π<T →
  (∀ z:ℂ,riemannZeta z=0 → 0<z.im → z.im≠T) →
  |ZeroCount.v1.zetaNClosed T-ZeroCount.v1.rvmMain T| ≤
    min (bptAllowance (log T)) (min (bwFirstAllowance (log T)) (bwSecondAllowance (log T)))
/-- Whole real lower-height regime; the smaller leading BW coefficient loses. -/
def bpt_better_low : Prop := ∀ L:ℝ,1≤L → L≤25 →
  bptAllowance L < bwFirstAllowance L ∧ bptAllowance L < bwSecondAllowance L
/-- Whole real high regime where the stronger SECOND BW bound beats BPT. -/
def bw_second_better_high : Prop := ∀ L:ℝ,32≤L → bwSecondAllowance L < bptAllowance L
/-- Whole real high regime for BW's first bound considered on its own. -/
def bw_first_better_high : Prop := ∀ L:ℝ,60≤L → bwFirstAllowance L < bptAllowance L
end ZeroCountEnvelope.v1
