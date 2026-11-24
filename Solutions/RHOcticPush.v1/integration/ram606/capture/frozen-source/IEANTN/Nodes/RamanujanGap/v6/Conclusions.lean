/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Nodes.RamanujanGap.v5.Conclusions
namespace RamanujanGap.v6
open Real IEANTN

/-- The full old profile is retained above610b; the new local margin is0.001. -/
noncomputable def profile (x : ℝ) : ℝ :=
  if (610000000000 : ℝ) ≤ x then RamanujanGap.v5.profile x else 1 / 1000

def local_606b : Prop := ∀ x : ℝ, 606000000000 ≤ x → x ≤ 610000000000 →
  (1 / 1000 : ℝ) * x^2 / (log x)^6 ≤ RamanujanGap.v1.gap x

def full_profile : Prop := ∀ x : ℝ, 606000000000 ≤ x →
  profile x * x^2 / (log x)^6 ≤ RamanujanGap.v1.gap x

def margin_606b : Prop := ∀ x : ℝ, 606000000000 ≤ x →
  (1 / 1000 : ℝ) * x^2 / (log x)^6 ≤ RamanujanGap.v1.gap x

def ramanujan : Prop := ∀ x : ℝ, 606000000000 ≤ x →
  primeCounting x^2 < exp 1 * x / log x * primeCounting (x / exp 1)

def retains_v5_profile : Prop := ∀ x : ℝ, 610000000000 ≤ x →
  profile x = RamanujanGap.v5.profile x

def retains_original_margin : Prop := ∀ x : ℝ, 640000000000 ≤ x →
  profile x = RamanujanGap.v3.profile x

def profile_gain : Prop :=
  (∀ x : ℝ, 607000000000 ≤ x → RamanujanGap.v5.profile x ≤ profile x) ∧
  ∀ x : ℝ, 607000000000 ≤ x → x < 610000000000 →
    RamanujanGap.v5.profile x < profile x
end RamanujanGap.v6
