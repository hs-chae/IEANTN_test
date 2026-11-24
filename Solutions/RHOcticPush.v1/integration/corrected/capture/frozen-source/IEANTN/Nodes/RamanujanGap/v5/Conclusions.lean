/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Nodes.RamanujanGap.v4.Conclusions
namespace RamanujanGap.v5
open Real IEANTN
/-- Entire original profile is retained from640b, including both tail maxima. -/
noncomputable def profile (x : ℝ) : ℝ :=
  if (640000000000:ℝ) ≤ x then RamanujanGap.v3.profile x
  else if (620000000000:ℝ) ≤ x then 1/80
  else if (619000000000:ℝ) ≤ x then 1/100
  else if (610000000000:ℝ) ≤ x then 1/1000
  else 1/10000
def margin_607b : Prop := ∀ x : ℝ, 607000000000 ≤ x →
  (1/10000:ℝ)*x^2/(log x)^6 ≤ RamanujanGap.v1.gap x
def full_profile : Prop := ∀ x : ℝ, 607000000000 ≤ x →
  profile x*x^2/(log x)^6 ≤ RamanujanGap.v1.gap x
def ramanujan : Prop := ∀ x : ℝ, 607000000000 ≤ x →
  primeCounting x^2 < exp 1*x/log x*primeCounting (x/exp 1)
def retains_original_margin : Prop := ∀ x : ℝ, 640000000000 ≤ x →
  profile x=RamanujanGap.v3.profile x
def profile_gain : Prop :=
  (∀ x : ℝ, 620000000000 ≤ x → RamanujanGap.v4.profile x ≤ profile x) ∧
  ∀ x : ℝ, 620000000000 ≤ x → x < 640000000000 →
    RamanujanGap.v4.profile x < profile x
end RamanujanGap.v5
