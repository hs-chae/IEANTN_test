/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitAffineWindow
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
open Real Set MeasureTheory
namespace RH080Next.Primal
open RH080Next.Explicit

private theorem hat_on_cell (i j : ℕ) (x : ℝ)
    (hlo : (j:ℝ)≤x) (hhi : x≤(j:ℝ)+1) :
    hat (x-i)=(if i=j then (j:ℝ)+1-x else 0)+
      (if i=j+1 then x-(j:ℝ) else 0) := by
  by_cases hij : i=j
  · subst i
    have hn : x-(j:ℝ)≥0 := by linarith
    have hb : 0≤1-(x-(j:ℝ)) := by linarith
    rw [ite_eq_left rfl,ite_eq_right (show j≠j+1 by omega),add_zero,
      hat,abs_of_nonneg hn,max_eq_right hb]
    ring
  by_cases his : i=j+1
  · subst i
    have hn : x-((j+1:ℕ):ℝ)≤0 := by push_cast; linarith
    rw [ite_eq_right (show j+1≠j by omega),ite_eq_left rfl,zero_add,
      hat,abs_of_nonpos hn,max_eq_right (by push_cast; linarith)]
    push_cast
    ring
  have hz : hat (x-i)=0 := by
    apply hat_eq_zero
    rcases lt_or_gt_of_ne hij with h | h
    · have hi : (i:ℝ)+1≤ j := by exact_mod_cast h
      exact (by linarith : (1:ℝ)≤x-i).trans (le_abs_self _)
    · have hi : (j:ℝ)+2≤ i := by exact_mod_cast (show j+2≤ i by omega)
      have hn : x-(i:ℝ)≤0 := by linarith
      rw [abs_of_nonpos hn]
      linarith
  simp [hij,his,hz]

/-- On the nonnegative half-line, the symmetric hat expression is exactly the
ordinary finite cardinal-hat sum including its checked zero terminal node. -/
theorem affineSpectrum_eq_cardinal_sum (nodes : List ℚ) (m : ℕ)
    (hlen : 2≤nodes.length) (hlast : node nodes (nodes.length-1)=0)
    (v : ℝ) (hx : 0≤(m:ℝ)*v) :
    affineSpectrum nodes m v=
      ∑ i ∈ Finset.range nodes.length, node nodes i*hat ((m:ℝ)*v-i) := by
  have hplus (i : ℕ) (hi : i∈Finset.Ico 1 (nodes.length-1)) :
      hat ((m:ℝ)*v+i)=0 := by
    apply hat_eq_zero
    have hi1 : (1:ℝ)≤ i := by exact_mod_cast (Finset.mem_Ico.mp hi).1
    exact (by linarith : (1:ℝ)≤(m:ℝ)*v+i).trans (le_abs_self _)
  have he : (∑ i ∈ Finset.Ico 1 (nodes.length-1),
      node nodes i*(hat ((m:ℝ)*v-i)+hat ((m:ℝ)*v+i))) =
      ∑ i ∈ Finset.Ico 1 (nodes.length-1), node nodes i*hat ((m:ℝ)*v-i) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hplus i hi,add_zero]
  unfold affineSpectrum
  rw [he,show nodes.length=(nodes.length-1)+1 by omega,
    Finset.sum_range_succ,hlast,zero_mul,add_zero,
    Finset.sum_range_eq_add_Ico _ (by omega : 0<nodes.length-1)]
  simp

/-- Exact interpolation follows from the actual finite-hat syntax, with both
closed cell endpoints and the outer terminal cell included. -/
theorem affineSpectrum_cell_phase (nodes : List ℚ) (m : ℕ)
    (hlen : 2≤nodes.length) (hlast : node nodes (nodes.length-1)=0)
    (j : ℕ) (hj : j<nodes.length-1) (v : ℝ)
    (hlo : (j:ℝ)≤(m:ℝ)*v) (hhi : (m:ℝ)*v≤(j:ℝ)+1) :
    affineSpectrum nodes m v=
      (1-((m:ℝ)*v-j))*node nodes j+((m:ℝ)*v-j)*node nodes (j+1) := by
  rw [affineSpectrum_eq_cardinal_sum nodes m hlen hlast v
    ((Nat.cast_nonneg j).trans hlo)]
  have hsum : (∑ i ∈ Finset.range nodes.length, node nodes i*hat ((m:ℝ)*v-i))=
      ∑ i ∈ Finset.range nodes.length,
        ((if i=j then node nodes i*((j:ℝ)+1-(m:ℝ)*v) else 0)+
          (if i=j+1 then node nodes i*((m:ℝ)*v-j) else 0)) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hat_on_cell i j ((m:ℝ)*v) hlo hhi,mul_add]
    split_ifs <;> simp_all
  rw [hsum,Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq',Finset.mem_range,
    ite_eq_left (show j<nodes.length by omega),ite_eq_left (show j+1<nodes.length by omega)]
  ring

/-- The physical mesh interval version of the exact same identity. -/
theorem affineSpectrum_cell (nodes : List ℚ) (m : ℕ)
    (hlen : 2≤nodes.length) (hm : 0<m) (hlast : node nodes (nodes.length-1)=0)
    (j : ℕ) (hj : j<nodes.length-1) (v : ℝ)
    (hv : v∈Icc ((j:ℝ)/(m:ℝ)) (((j:ℝ)+1)/(m:ℝ))) :
    affineSpectrum nodes m v=
      (1-((m:ℝ)*v-j))*node nodes j+((m:ℝ)*v-j)*node nodes (j+1) := by
  have hm' : (0:ℝ)<m := by exact_mod_cast hm
  apply affineSpectrum_cell_phase nodes m hlen hlast j hj v
  · nlinarith [(div_le_iff₀ hm').mp hv.1]
  · nlinarith [(le_div_iff₀ hm').mp hv.2]

#print axioms affineSpectrum_eq_cardinal_sum
#print axioms affineSpectrum_cell_phase
#print axioms affineSpectrum_cell
end RH080Next.Primal
