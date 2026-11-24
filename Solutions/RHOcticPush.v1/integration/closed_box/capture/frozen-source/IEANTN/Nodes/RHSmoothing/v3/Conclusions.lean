/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Nodes.RHSmoothing.v2.Conclusions
namespace RHSmoothing.v3
/-- Exact previous improved whole Box psi function; the new source graph now
constructs every former Box analytic obligation from actual providers. -/
def box_psi : Prop := RHSmoothing.v2.box_psi
/-- Exact previous uniform strict correction gain, preserved unchanged. -/
def box_gain : Prop := RHSmoothing.v2.box_gain
end RHSmoothing.v3
