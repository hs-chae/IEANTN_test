/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import AnalyticFlatFamilyDirichlet
import ExplicitBRPopulationConsumer
import ExplicitAffineIntegrals
import ExplicitCMSEligible
import AffinePopulationBounds

set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open Real MeasureTheory RH080Next.Explicit
open scoped BigOperators
namespace RH080Next.AnalyticFlatFamily

def nodes (m : ℕ) : List ℚ := (List.range (5*m+1)).map (fun j=>if j<m then (1:ℚ) else 0)

theorem nodes_length (m : ℕ) : (nodes m).length=5*m+1 := by simp [nodes]

theorem node_eq (m j : ℕ) : node (nodes m) j=if j<m then 1 else 0 := by
  unfold node nodes
  by_cases hj : j<5*m+1
  · rw [List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range hj]
    simp only [Option.map_some,Option.getD_some]
    split <;> norm_num
  · rw [List.getD_eq_default _ _ (by simpa using hj)]
    have h : ¬j<m := by omega
    simp [h]

theorem terminal_zero (m : ℕ) : node (nodes m) (5*m)=0 := by
  rw [node_eq,if_neg (by omega)]

theorem sum_node_mul (m : ℕ) (f : ℕ→ℝ) :
    (∑j∈Finset.Ico (1:ℕ) (5*m),node (nodes m) j*f j)=∑j∈Finset.Ico (1:ℕ) m,f j := by
  symm
  calc
    _ = ∑j∈Finset.Ico (1:ℕ) m,node (nodes m) j*f j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [node_eq,if_pos (Finset.mem_Ico.mp hj).2,one_mul]
    _ = _ := by
      apply Finset.sum_subset
      · intro j hj
        simp only [Finset.mem_Ico] at *
        omega
      · intro j hj hnot
        have h : ¬j<m := by simp only [Finset.mem_Ico] at *; omega
        rw [node_eq,if_neg h,zero_mul]

theorem polynomial_identity (m : ℕ) (hm : 0<m) (t : ℝ) :
    nodalPolynomial (nodes m) t=poly m t := by
  unfold nodalPolynomial poly
  rw [nodes_length]
  simp only [Nat.add_sub_cancel]
  rw [sum_node_mul,node_eq,if_pos hm]

theorem normalization (m : ℕ) (hm : 0<m) : nodalF0 (nodes m) m=order m/(m:ℝ) := by
  unfold nodalF0
  rw [nodes_length]
  simp only [Nat.add_sub_cancel]
  have hs:=sum_node_mul m (fun _=>1)
  simp only [mul_one] at hs
  rw [hs,node_eq,if_pos hm]
  simp only [Finset.sum_const,Nat.card_Ico,Nat.cast_sub (by omega : 1≤m),Nat.cast_one,nsmul_eq_mul,mul_one]
  unfold order
  ring

theorem actual_F0 (m : ℕ) (hm : 0<m) :
    inverseCosine (affineSpectrum (nodes m) m) 0=order m/(m:ℝ) := by
  rw [inverseCosine_zero,integral_affineSpectrum _ _ hm,normalization m hm]

theorem window_bound (m : ℕ) (hm : 0<m) (v : ℝ) :
    |affineSpectrum (nodes m) m v|≤1 := by
  apply RH080Next.Primal.affineSpectrum_abs_le (nodes m) m 1
    (by rw [nodes_length]; omega) (by norm_num)
  intro j _
  rw [node_eq]
  split <;> norm_num

theorem attained_maximum (m : ℕ) (hm : 0<m) :
    ∃v:ℝ,|affineSpectrum (nodes m) m v|=1 := by
  refine ⟨0,?_⟩
  rw [affineSpectrum_zero,node_eq,if_pos hm]
  norm_num

theorem leakage_zero (m : ℕ) (hm : 0<m) :
    IEANTN.CMSFunctional.positiveLeak (affineSpectrum (nodes m) m)=0 := by
  unfold IEANTN.CMSFunctional.positiveLeak IEANTN.CMSFunctional.exterior
  rw [RH080Next.Primal.affineSpectrum_single_boundary_leak (nodes m) m hm
    (by rw [nodes_length]; omega)]
  · rw [node_eq,if_neg (by omega),zero_div]
  · intro j hj
    rw [node_eq,if_neg (by omega)]
  · rw [node_eq,if_neg (by omega)]

theorem denominator (m : ℕ) (hm : 0<m) :
    brDenominatorFour (nodes m) m=order m/(m:ℝ) := by
  unfold brDenominatorFour
  rw [actual_F0 m hm,leakage_zero m hm]
  ring

theorem actual_eligible (m : ℕ) (hm : 0<m) :
    IEANTN.CMSFunctional.Eligible (inverseCosine (affineSpectrum (nodes m) m))
      (affineSpectrum (nodes m) m) := by
  have horder : 0<order m := lt_of_lt_of_le (by norm_num) (order_ge_one m hm)
  have hmR : 0<(m:ℝ) := by exact_mod_cast hm
  apply affine_inverse_eligible (nodes m) m (by rw [nodes_length]; omega) hm
    (by rw [nodes_length]; exact terminal_zero m)
  rw [normalization m hm]
  exact (div_pos horder hmR).ne'

#print axioms polynomial_identity
#print axioms denominator
#print axioms actual_eligible
end RH080Next.AnalyticFlatFamily
