/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Vocabulary.GoldbachCount

/-! Exact mathematical interface of the computation-led count128 experiment.
This is a new representation-count property, not a larger verified Goldbach prefix.
The source contract, complete main/safety proof, exact accepted execution and trust
tier are recorded in the accompanying metadata and reproducibility bundle. -/
namespace GoldbachCountNumerics.v1

/-- At least128 distinct unordered prime pairs for every even n in
[1000000,2000000000], with smaller prime at most65535.
Original experiment parameters: A=1000000,B=2000000000,P=65535,K=128;
999500001 targets, all included. No optimality or global-best assertion. -/
def count_128_on_window : Prop :=
  IEANTN.GoldbachCountOn 1000000 2000000000 65535 128

end GoldbachCountNumerics.v1
