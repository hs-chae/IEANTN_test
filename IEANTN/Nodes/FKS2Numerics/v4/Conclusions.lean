/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Nodes.FKS2Numerics.v3.Conclusions
namespace FKS2Numerics.v4
/-- The QRH-updated multiplier: `ν*(10⁻¹⁰, 300) ≤ 2·10⁻⁴⁹`, with ψ constant `10⁻¹⁰` from the QRH
propagation. `FKS2.v5` consumes it for prime intervals `(x, x + x/10¹³]` for `x ≥ e^300`. Same
program shape as `FKS2Numerics.v3.baseline_bound`, with updated source `c/updated.c`. Local gate
and native facts are in `pv-evidence/`. -/
def updated_bound : Prop := FKS2Numerics.v3.nuStar 0.0000000001 300 ≤ (2:ℝ)/10^49
end FKS2Numerics.v4
