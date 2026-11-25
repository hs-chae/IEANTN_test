/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Nodes.ZeroCount.v1.Conclusions
namespace BellottiWongZeroCount.v1
open Real
/-- The source's main term has NO7/8. On T>0 this expanded expression equals
T/(2*pi)*log (T/(2*pi*exp1)); the Solution proves the identity explicitly. -/
noncomputable def mainWithoutConstant (T:ℝ) : ℝ :=
  T/(2*π)*log (T/(2*π))-T/(2*π)
/-- **BW2025 Theorem1.1 first bound**, arXiv2412.15470v2,07Jul2025,
DOI10.1090/mcom/4133. Counts 0<Imrho<=T with multiplicity, ordinary zero count,
no RH assumption. T>=e inclusive. Published constant8.08344, notv1's8.08292. -/
def bound_first : Prop := ∀ T:ℝ, exp 1 ≤ T →
  |ZeroCount.v1.zetaNClosed T-mainWithoutConstant T| ≤
    (2519/25000:ℝ)*log T+(1223/5000:ℝ)*log (log T)+202086/25000
/-- **Theorem1.1 second bound**, same center/count/domain. It improves on the
first on a large finite-height range despite the larger leading coefficient. -/
def bound_second : Prop := ∀ T:ℝ, exp 1 ≤ T →
  |ZeroCount.v1.zetaNClosed T-mainWithoutConstant T| ≤
    (14/125:ℝ)*log T+(12567/100000:ℝ)*log (log T)+377417/100000
end BellottiWongZeroCount.v1
