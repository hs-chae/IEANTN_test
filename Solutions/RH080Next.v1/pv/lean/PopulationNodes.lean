/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import PopulationModel
import ExplicitAffineFourier
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace RH080Next.PopulationPV
open RH080Next.Explicit Real

/-- Original m8/R2 mathematical window, with its explicit terminal zero. -/
def nodes : List ℚ :=
  Model.coefficients.map (fun a => (a : ℚ)/1000000000000000000) ++ [0]

theorem nodes_length : nodes.length = 17 := by decide +kernel

theorem nodes_terminal : node nodes 16 = 0 := by norm_num [nodes,node,Model.coefficients]

theorem polynomial_identity (y : ℝ) :
    nodalPolynomial nodes y = Model.trigPolynomial y := by
  norm_num [nodalPolynomial,node,nodes,Model.trigPolynomial,Model.coefficients,
    Model.coefficient,Model.weight,Finset.sum_range_succ,Finset.sum_Ico_eq_sum_range]
  <;> ring

theorem nodal_normalization : nodalF0 nodes 8 = 1 := by
  norm_num [nodalF0,node,nodes,Model.coefficients,Finset.sum_Ico_eq_sum_range,
    Finset.sum_range_succ]

#print axioms polynomial_identity
#print axioms nodal_normalization
end RH080Next.PopulationPV
