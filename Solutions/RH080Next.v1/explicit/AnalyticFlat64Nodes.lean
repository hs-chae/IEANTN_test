/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import AnalyticFlat64Dirichlet
import ExplicitBRPopulationConsumer
import ExplicitAffineIntegrals
import AffinePopulationBounds

set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open Real MeasureTheory RH080Next.Explicit
open scoped BigOperators
namespace RH080Next.AnalyticFlat64

/-- Fixed rational support-five source class; only the first64 nodes are nonzero. -/
def nodes : List ℚ := (List.range 321).map (fun j=>if j<64 then (1:ℚ) else 0)

theorem nodes_length : nodes.length=321 := by simp [nodes]

theorem node_eq (j : ℕ) : node nodes j=if j<64 then 1 else 0 := by
  unfold node nodes
  by_cases hj : j<321
  · rw [List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range hj]
    simp only [Option.map_some,Option.getD_some]
    split <;> norm_num
  · rw [List.getD_eq_default _ _ (by simpa using hj)]
    have h64 : ¬j<64 := by omega
    simp [h64]

theorem terminal_zero : node nodes 320=0 := by rw [node_eq]; norm_num

theorem sum_node_mul (f : ℕ→ℝ) :
    (∑ j∈Finset.Ico (1:ℕ) 320,node nodes j*f j)=∑ j∈Finset.Ico (1:ℕ) 64,f j := by
  symm
  calc
    _ = ∑ j∈Finset.Ico (1:ℕ) 64,node nodes j*f j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [node_eq,if_pos (Finset.mem_Ico.mp hj).2,one_mul]
    _ = _ := by
      apply Finset.sum_subset
      · intro j hj
        simp only [Finset.mem_Ico] at *
        omega
      · intro j hj hnot
        have h64 : ¬j<64 := by simp only [Finset.mem_Ico] at *; omega
        rw [node_eq,if_neg h64,zero_mul]

theorem polynomial_identity (t : ℝ) : nodalPolynomial nodes t=poly t := by
  unfold nodalPolynomial poly
  rw [nodes_length]
  norm_num only [Nat.reduceSub]
  rw [sum_node_mul, node_eq]
  norm_num

theorem normalization : nodalF0 nodes 64=(127:ℝ)/64 := by
  unfold nodalF0
  rw [nodes_length]
  norm_num only [Nat.reduceSub]
  have hs := sum_node_mul (fun _=>1)
  simp only [mul_one] at hs
  rw [hs,node_eq]
  norm_num

theorem actual_F0 : inverseCosine (affineSpectrum nodes 64) 0=(127:ℝ)/64 := by
  unfold inverseCosine
  simp only [mul_zero,zero_mul,cos_zero,mul_one]
  rw [integral_affineSpectrum nodes 64 (by norm_num),normalization]

theorem window_bound (v : ℝ) : |affineSpectrum nodes 64 v|≤1 := by
  apply RH080Next.Primal.affineSpectrum_abs_le nodes 64 1 (by rw [nodes_length]; norm_num) (by norm_num)
  intro j _
  rw [node_eq]
  split <;> norm_num

theorem attained_maximum : ∃v:ℝ,|affineSpectrum nodes 64 v|=1 := by
  refine ⟨0,?_⟩
  rw [affineSpectrum_zero,node_eq]
  norm_num

theorem leakage_zero : IEANTN.CMSFunctional.positiveLeak (affineSpectrum nodes 64)=0 := by
  unfold IEANTN.CMSFunctional.positiveLeak IEANTN.CMSFunctional.exterior
  rw [RH080Next.Primal.affineSpectrum_single_boundary_leak nodes 64 (by norm_num)
    (by rw [nodes_length]; norm_num)]
  · rw [node_eq]; norm_num
  · intro j hj
    rw [node_eq,if_neg (by omega)]
  · rw [node_eq]; norm_num

theorem denominator : brDenominatorFour nodes 64=(127:ℝ)/64 := by
  unfold brDenominatorFour
  rw [actual_F0,leakage_zero]
  ring

#print axioms polynomial_identity
#print axioms denominator
#print axioms window_bound
end RH080Next.AnalyticFlat64
