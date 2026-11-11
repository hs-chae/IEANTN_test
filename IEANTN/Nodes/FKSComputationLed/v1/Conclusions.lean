/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/

import IEANTN.Vocabulary.ErrorTerms

/-! A new finite-window numerical PNT application. The offset logarithmic integral
is exactly `IEANTN.Li`. This is an internally constructed result, not a statement
attributed to FKS2 or Büthe. Those papers are comparison sources only.
The solution discloses native-assisted finite numerical execution. -/
namespace FKSComputationLed.v1
open Real IEANTN
def finite_pi_li : Prop := ∀x:ℝ, 100000000≤x → x≤1000000000 →
  |primeCounting x-Li x|≤(19/10:ℝ)*sqrt x/log x
def finite_relative_error : Prop := ∀x:ℝ, 100000000≤x → x≤1000000000 →
  Eπ x≤(19/10:ℝ)/sqrt x
end FKSComputationLed.v1
