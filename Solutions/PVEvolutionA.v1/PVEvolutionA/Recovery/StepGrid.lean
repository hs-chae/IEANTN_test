/- Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
/- Finite, ordered lower envelopes and refinement; no analytic source assumptions. -/
import PVEvolutionA.Graded
namespace PVEvolutionA.Recovery.StepGrid
open Real WinnerDensityA WinnerDensityA.Program
set_option maxHeartbeats 0
noncomputable def weighted (a c : Nat→ℝ) (n : Nat) (L : ℝ) : ℝ :=
  exp (L*(a 0-7/8))*c 0+
    ∑ i∈Finset.range n, (exp (L*(a (i+1)-7/8))-exp (L*(a i-7/8)))*c i

theorem telescope (w c : Nat→ℝ) (n : Nat) :
    w 0*c 0+∑ i∈Finset.range n, (w (i+1)-w i)*c i=
      w n*c n+∑ i∈Finset.range n, w (i+1)*(c i-c (i+1)) := by
  induction n with
  | zero => simp
  | succ n ih => simp only [Finset.sum_range_succ];rw [←add_assoc,ih];ring

theorem antitone (a c : Nat→ℝ) (n : Nat)
    (ha : ∀ i≤n, a i≤7/8) (hc : ∀ i<n, c (i+1)≤c i) (hlast : a n=7/8)
    {L U : ℝ} (hLU : L≤U) : weighted a c n U≤weighted a c n L := by
  unfold weighted
  rw [telescope (fun i=>exp (U*(a i-7/8))) c n,
    telescope (fun i=>exp (L*(a i-7/8))) c n,hlast]
  simp only [sub_self,mul_zero,exp_zero,one_mul]
  apply add_le_add_right
  apply Finset.sum_le_sum
  intro i hi
  have hin : i<n := Finset.mem_range.mp hi
  apply mul_le_mul_of_nonneg_right
  · apply exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_right hLU (sub_nonpos.mpr (ha (i+1) hin))
  · exact sub_nonneg.mpr (hc i hin)

theorem sum_blocks (f : Nat→ℝ) (n m : Nat) :
    ∑ i∈Finset.range (n*m), f i =
      ∑ j∈Finset.range n, ∑ k∈Finset.range m, f (j*m+k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.succ_mul,Finset.sum_range_add,ih,Finset.sum_range_succ]

theorem sum_differences (w : Nat→ℝ) (i m : Nat) :
    ∑ k∈Finset.range m, (w (i+k+1)-w (i+k))=w (i+m)-w i := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ,ih];simp only [Nat.add_succ];ring

theorem refinement_lower (a : Nat→ℝ) (Q : ℝ→ℝ) (c : Nat→ℝ) (n m : Nat)
    (ha : Monotone a) {L : ℝ} (hL : 0≤L)
    (hbase : c 0≤Q (a 0))
    (hc : ∀ j<n, ∀ k<m, c j≤Q (a (j*m+k))) :
    weighted (fun j=>a (j*m)) c n L≤gridCoefficient Q a (n*m) L := by
  unfold weighted gridCoefficient
  simp only [Nat.zero_mul]
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left hbase (exp_pos _).le
  · rw [sum_blocks]
    apply Finset.sum_le_sum
    intro j hj
    have hjn:=Finset.mem_range.mp hj
    calc
      _ = (∑ k∈Finset.range m,
          (exp (L*(a (j*m+k+1)-7/8))-exp (L*(a (j*m+k)-7/8))))*c j := by
            rw [sum_differences (fun i=>exp (L*(a i-7/8))) (j*m) m]
            simp only [Nat.add_mul,Nat.one_mul]
      _ = ∑ k∈Finset.range m,
          (exp (L*(a (j*m+k+1)-7/8))-exp (L*(a (j*m+k)-7/8)))*c j :=
            Finset.sum_mul _ _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro k hk
        apply mul_le_mul_of_nonneg_left (hc j hjn k (Finset.mem_range.mp hk))
        exact sub_nonneg.mpr (exp_le_exp.mpr
          (mul_le_mul_of_nonneg_left (sub_le_sub_right (ha (Nat.le_succ _)) _) hL))

theorem graded_refinement {n m : Nat} (hn : 0<n) (hm : 0<m) (j : Nat) :
    gradedGrid (n*m) (j*m)=gradedGrid n j := by
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  have hm0 : (m:ℝ)≠0 := by exact_mod_cast hm.ne'
  unfold gradedGrid
  rw [←Nat.sub_mul]
  push_cast
  field_simp
  <;> ring
#print axioms antitone
#print axioms refinement_lower
end PVEvolutionA.Recovery.StepGrid
