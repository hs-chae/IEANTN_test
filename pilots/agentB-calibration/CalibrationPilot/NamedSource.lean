/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Agent B (Claude), integration workstream
-/
import ForwardRamanujan.Source

/-!
# A named variant of the frozen selected-sum wrapper

`ForwardRamanujan.renderProgram` (frozen, `Solutions/RamanujanNumerics.v1`) always renders the
entry point `ramanujan_epsilon_bound`. The calibration program A computes something else, so it gets
its own entry-point name. Only the source-text association changes: the execution relation is the
frozen one, and soundness is the frozen `ForwardRamanujan.source_linked_upper`, reached through
`to_exec` below. Nothing in the frozen files is copied or modified.
-/

namespace CalibrationPilot
open FKS2Scalar FKS2Table4 SumStability ForwardRamanujan

/-- The frozen rendering with the entry-point name replaced. -/
def renderNamed (name : String) (p : Program) : String :=
  (SumStability.render selectedSumProgram).getD "" ++
  "static const double inputs[" ++ toString p.inputs.length ++ "] = {" ++
  String.intercalate "," p.inputs ++ "};" ++
  "double " ++ name ++ "(void) { double s = sum(inputs," ++
  toString p.inputs.length ++ "); double r = (s * " ++ p.scale ++ ");" ++
  "r = (r - " ++ p.fixedOffset ++ "); r = (r - " ++ p.positiveOffset ++ "); return r; }"

/-- Token-level association of an actual source text with the named rendering. -/
def sourceMatchesNamed (src name : String) (p : Program) : Bool :=
  let ts := ForwardRamanujan.tokens src
  ts.isSome && ts == ForwardRamanujan.tokens (renderNamed name p)

/-- The frozen execution relation, with the named source association in place of the fixed one. -/
def ExecNamed (src name : String) (p : Program) (initial : CState) (out : ℚ) : Prop :=
  sourceMatchesNamed src name p = true ∧ 1 ≤ p.inputs.length ∧ p.inputs.length ≤ 64 ∧
  ∃ xs s final,
    p.inputs.mapM loadLiteral = some xs ∧ RepresentsInput initial xs ∧
    runSum xs 0 = some s ∧ ExecC selectedSumProgram initial final s ∧
    suffix p s = some out ∧ SuffixIEEE p s out

/-- Everything after source association is literally the frozen `Exec`; the canonical rendering
matches itself whenever it tokenizes. This lets the frozen soundness theorem be reused as is. -/
theorem to_exec {src name : String} {p : Program} {initial : CState} {out : ℚ}
    (he : ExecNamed src name p initial out)
    (hcanon : (ForwardRamanujan.tokens (renderProgram p)).isSome = true) :
    Exec (renderProgram p) p initial out := by
  obtain ⟨_, h1, h2, rest⟩ := he
  refine ⟨?_, h1, h2, rest⟩
  simp [sourceMatches, hcanon]

end CalibrationPilot
