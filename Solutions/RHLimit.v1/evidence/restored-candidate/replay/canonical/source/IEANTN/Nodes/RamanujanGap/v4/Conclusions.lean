/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Nodes.RamanujanGap.v3.Conclusions
namespace RamanujanGap.v4
open Real IEANTN
noncomputable def profile (x : ℝ) : ℝ :=
  if 640000000000 ≤ x then RamanujanGap.v3.profile x else 1/1000
def margin_620b : Prop := ∀ x : ℝ, 620000000000 ≤ x →
  (1/1000:ℝ)*x^2/(log x)^6 ≤ RamanujanGap.v1.gap x
def full_profile : Prop := ∀ x : ℝ, 620000000000 ≤ x →
  profile x*x^2/(log x)^6 ≤ RamanujanGap.v1.gap x
def ramanujan : Prop := ∀ x : ℝ, 620000000000 ≤ x →
  primeCounting x^2 < exp 1*x/log x*primeCounting (x/exp 1)
def retains_original_margin : Prop := ∀ x : ℝ, 640000000000 ≤ x →
  profile x = RamanujanGap.v3.profile x
end RamanujanGap.v4
