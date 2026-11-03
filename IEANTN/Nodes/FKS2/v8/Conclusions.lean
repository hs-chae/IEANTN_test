/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Vocabulary.ErrorTerms

/-! Published FKS2 Table3 whole-tail numerical premises, not newly verified C data. -/
namespace FKS2.v8
open Real IEANTN
/-- FKS2 Definition5/Proposition17/Table3 row300; entire-tail allowance, without interpolation. -/
def table3_theta_300 : Prop := HasNumericalBound Eθ 1.6930e-12 (exp 300)
/-- FKS2 Definition5/Proposition17/Table3 row310; entire-tail allowance, without interpolation. -/
def table3_theta_310 : Prop := HasNumericalBound Eθ 1.6882e-12 (exp 310)
/-- FKS2 Definition5/Proposition17/Table3 row320; entire-tail allowance, without interpolation. -/
def table3_theta_320 : Prop := HasNumericalBound Eθ 1.6837e-12 (exp 320)
/-- FKS2 Definition5/Proposition17/Table3 row330; entire-tail allowance, without interpolation. -/
def table3_theta_330 : Prop := HasNumericalBound Eθ 1.6795e-12 (exp 330)
end FKS2.v8
