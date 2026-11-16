/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Nodes.OpenAIQRH.v1.Conclusions
import IEANTN.Nodes.ZetaHadamard.v2.Conclusions
import IEANTN.Nodes.ZetaLogDeriv.v2.Conclusions
import Mathlib.Tactic

/-! The original identities with their nonvanishing guards supplied by QRH. -/
namespace QRHIdentities

theorem partial_fractions (hqrh : OpenAIQRH.v1.zeta_seven_eighths)
    (hH : ZetaHadamard.v1.logDeriv_partial_fractions) :
    ZetaHadamard.v2.halfplane_partial_fractions := by
  intro s w hs hw hs1 hw1
  exact hH s w hs1 hw1 (hqrh s hs hs1) (hqrh w hw hw1)

theorem functional_equation (hqrh : OpenAIQRH.v1.zeta_seven_eighths)
    (hfe : ZetaLogDeriv.v1.logDeriv_functional_equation) :
    ZetaLogDeriv.v2.halfplane_functional_equation := by
  intro s hs hs1 hcos
  apply hfe s
  · intro n hn
    have hr := congrArg Complex.re hn
    simp only [Complex.neg_re, Complex.natCast_re] at hr
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  · exact hs1
  · exact hqrh s hs hs1
  · exact hcos

end QRHIdentities
