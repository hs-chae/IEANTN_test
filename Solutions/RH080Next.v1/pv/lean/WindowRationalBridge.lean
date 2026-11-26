/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import WindowAffineData
import WindowModel
import ExplicitAffineWindow
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace RH080Next.WindowPV
open RH080Next.Explicit

def qnode (nodes : List ℚ) (j : ℕ) : ℚ := nodes.getD j 0

def qF0 (nodes : List ℚ) (m : ℕ) : ℚ :=
  (qnode nodes 0 + 2 * ∑ j ∈ Finset.Ico 1 (nodes.length - 1), qnode nodes j) / m

def qH (nodes : List ℚ) (m : ℕ) : ℚ :=
  max 0 (qnode nodes m) + ∑ j ∈ Finset.Ico m (nodes.length - 1),
    max 0 (max 0 (qnode nodes (j+1)) - max 0 (qnode nodes j))

def qV1 (nodes : List ℚ) (m : ℕ) : ℚ :=
  2 * m * (|qnode nodes 1 - qnode nodes 0| +
    (∑ j ∈ Finset.Ico 1 (nodes.length - 1),
      |qnode nodes (j+1) - 2 * qnode nodes j + qnode nodes (j-1)|) +
    |qnode nodes (nodes.length-1) - qnode nodes (nodes.length-2)|)

def qMu2 (nodes : List ℚ) (m : ℕ) : ℚ :=
  (∑ j ∈ Finset.range (nodes.length - 1),
    ((6 * (j : ℚ)^2 + 4*j + 1) * |qnode nodes j| +
      (6 * (j : ℚ)^2 + 8*j + 3) * |qnode nodes (j+1)|)) / (6 * (m : ℚ)^3)

theorem qF0_cast (nodes : List ℚ) (m : ℕ) :
    (qF0 nodes m : ℝ) = nodalF0 nodes m := by
  unfold qF0 nodalF0 qnode node
  push_cast
  rfl

theorem qH_cast (nodes : List ℚ) (m : ℕ) :
    (qH nodes m : ℝ) = nodalH nodes m := by
  unfold qH nodalH qnode node
  push_cast
  rfl

theorem qV1_cast (nodes : List ℚ) (m : ℕ) :
    (qV1 nodes m : ℝ) = nodalV1 nodes m := by
  unfold qV1 nodalV1 qnode node
  push_cast
  rfl

theorem qMu2_cast (nodes : List ℚ) (m : ℕ) :
    (qMu2 nodes m : ℝ) = nodalMu2Upper nodes m := by
  unfold qMu2 nodalMu2Upper qnode node
  push_cast
  rfl

/-- Independent rational evaluation of the original mathematical nodal object.
These are not execution claims; actual source execution is proved separately. -/
theorem actual_qF0 : qF0 Data.affineNodes 360 =
    3599999999999999998 / (360*10000000000000000) := by decide +kernel

theorem actual_qH : qH Data.affineNodes 360 =
    1146154494119977 / 10000000000000000 := by decide +kernel

theorem actual_qV1 : qV1 Data.affineNodes 360 =
    40713308729275680 / 10000000000000000 := by decide +kernel

theorem actual_qMu2 : qMu2 Data.affineNodes 360 ≤
    69452659995205718 / (6*360^3*1000000000) := by decide +kernel

#print axioms qF0_cast
#print axioms qH_cast
#print axioms qV1_cast
#print axioms qMu2_cast
#print axioms actual_qF0
#print axioms actual_qH
#print axioms actual_qV1
#print axioms actual_qMu2
end RH080Next.WindowPV
