/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FKS2Table4.Result
import IEANTN.Nodes.FKS2.v6.Conclusions
import IEANTN.Nodes.FKS2Numerics.v5.Conclusions

theorem FKS2Numerics.v5.challenge_numerical_pi
    (hP : QRHCH2.v5.psi_refined_bound) (hOld : FKS2.v6.table4_anchor_300) :
    FKS2Numerics.v5.numerical_pi := FKS2Table4.numerical_pi hP hOld
