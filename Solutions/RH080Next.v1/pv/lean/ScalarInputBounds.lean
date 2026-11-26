/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import AffinePopulationBounds
import Mathlib.Data.List.GetD
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.ScalarInputBounds
open RH080Next.Explicit

def qMassA0 (nodes : List ℚ) (m : ℕ) : ℚ :=
  (|nodes.getD 0 0|+2*∑j∈Finset.Ico 1 (nodes.length-1),|nodes.getD j 0|)/(m:ℚ)

def qV0 (nodes : List ℚ) : ℚ :=
  2*∑j∈Finset.range (nodes.length-1),|nodes.getD (j+1) 0-nodes.getD j 0|

theorem qMassA0_cast (nodes : List ℚ) (m : ℕ) :
    (qMassA0 nodes m : ℝ)=nodalMassA0 nodes m := by
  unfold qMassA0 nodalMassA0 node
  push_cast
  rfl

theorem qV0_cast (nodes : List ℚ) : (qV0 nodes : ℝ)=nodalV0 nodes := by
  unfold qV0 nodalV0 node
  push_cast
  rfl

theorem node_abs_bound (nodes : List ℚ) (M : ℚ)
    (hall : ∀a∈nodes,|a|≤M) (j : ℕ) (hj : j<nodes.length) :
    |node nodes j|≤(M:ℝ) := by
  have h := hall nodes[j] (List.getElem_mem hj)
  have he : nodes.getD j 0=nodes[j] := List.getD_eq_getElem nodes 0 hj
  unfold node
  rw [he]
  exact_mod_cast h

#print axioms qMassA0_cast
#print axioms qV0_cast
#print axioms node_abs_bound
end RH080Next.ScalarInputBounds
