/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FapData
import Mathlib.Data.List.GetD
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace RH080Next.FapPV.Data

/-- Actual locked Fap400 mathematical nodes, including the terminal zero at j=400.
The C lookup returns this same zero by its out-of-range input branch. -/
def affineNodes : List ℚ := nodes ++ [0]

theorem nodes_length : nodes.length = 400 := by
  simp only [nodes, List.length_map, List.length_range, encoded_length]

theorem affineNodes_length : affineNodes.length = 401 := by
  simp [affineNodes, nodes_length]

theorem affineNodes_terminal : affineNodes.getLast? = some 0 := by
  simp [affineNodes]

theorem affineNodes_eq_map : affineNodes =
    (List.range 401).map rationalNode := by
  have hz : rationalNode 400 = 0 := by
    unfold rationalNode integerNode encodedNode
    rw [List.getElem?_eq_none (by rw [encoded_length])]
    simp
  have hr : List.range 401 = List.range 400 ++ [400] := List.range_succ
  change (List.range 400).map rationalNode ++ [0] = (List.range 401).map rationalNode
  rw [hr, List.map_append]
  simp only [List.map_singleton, hz]

#print axioms affineNodes_length
#print axioms affineNodes_terminal
#print axioms affineNodes_eq_map
end RH080Next.FapPV.Data
