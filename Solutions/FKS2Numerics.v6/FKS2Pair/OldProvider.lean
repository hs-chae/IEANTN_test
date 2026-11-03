/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FKS2Pair.OldResult
import IEANTN.Nodes.FKS2.v8.Conclusions
import IEANTN.Nodes.FKS2.v6.Conclusions
import IEANTN.Nodes.FKS2Numerics.v6.Conclusions

theorem FKS2Numerics.v6.challenge_old_pi
    (h300 : FKS2.v8.table3_theta_300) (h310 : FKS2.v8.table3_theta_310)
    (h320 : FKS2.v8.table3_theta_320) (h330 : FKS2.v8.table3_theta_330)
    (hAnchor : FKS2.v6.table4_anchor_300) : FKS2Numerics.v6.old_pi :=
  FKS2Pair.Old.numerical_pi h300 h310 h320 h330 hAnchor
