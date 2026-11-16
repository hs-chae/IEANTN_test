/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Nodes.FKS2.v2.Conclusions
import IEANTN.Nodes.BKLNW.v1.Conclusions

/-! Conservative extension of the original FKS2 correction, with coefficient anchor30 fixed.
The application threshold L is independent of that coefficient anchor. -/
namespace FKS2Numerics.v3
open IEANTN Real

noncomputable def nuStar (A L : ℝ) : ℝ :=
  FKS2.v2.nuAsymp A (3 / 2) 2 5.5666305 (1 + 1.93378e-8) (BKLNW.v1.a₂ 30) (exp L)

/-- Preserved historical mathematical instance; the original raw constant is unchanged. -/
def calibration_bound : Prop := nuStar 121.096 30 ≤ 6.339e-7

/-- Baseline numerical obligation on the common exp300tail, before any QRH update. -/
def baseline_bound : Prop := nuStar 121.096 300 ≤ (11 : ℝ) / 10 ^ 62

end FKS2Numerics.v3
