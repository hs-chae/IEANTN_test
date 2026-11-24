/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Nodes.RHPrimeCounting.v3.Conclusions
namespace RHPrimeCounting.v4
/-- Exact ordinary pi/Li2 whole envelope, consuming the fully supplied Box
analytic chain and the independently evolved GM transfer. -/
def box_Li : Prop := RHPrimeCounting.v3.box_Li
/-- Exact complete two-endpoint ordinary prime-count difference bound. -/
def box_interval : Prop := RHPrimeCounting.v3.box_interval
end RHPrimeCounting.v4
