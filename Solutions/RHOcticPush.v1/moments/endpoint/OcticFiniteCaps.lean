import OcticCellSound
import OcticCellTotals
import OcticMomentAssembly
namespace RHOcticPush.Moments.Endpoint
open Real Set MeasureTheory Finset
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

lemma grid_step (i : Nat) : grid i < grid (i+1) := by
  by_cases h0 : i < 1000
  · have hi : i ≤ 1000 := by omega
    have hi' : i+1 ≤ 1000 := by omega
    simp only [grid,if_pos hi,if_pos hi']
    push_cast
    linarith
  by_cases he0 : i=1000
  · subst i
    norm_num [grid]
  by_cases h1 : i < 2800
  · have hi : ¬i ≤ 1000 := by omega
    have hi' : ¬i+1 ≤ 1000 := by omega
    have hj : i ≤ 2800 := by omega
    have hj' : i+1 ≤ 2800 := by omega
    simp only [grid,if_neg hi,if_neg hi',if_pos hj,if_pos hj']
    rw [show i+1-1000=i-1000+1 by omega]
    push_cast
    linarith
  by_cases he1 : i=2800
  · subst i
    norm_num [grid]
  have hi : ¬i ≤ 1000 := by omega
  have hi' : ¬i+1 ≤ 1000 := by omega
  have hj : ¬i ≤ 2800 := by omega
  have hj' : ¬i+1 ≤ 2800 := by omega
  simp only [grid,if_neg hi,if_neg hi',if_neg hj,if_neg hj']
  rw [show i+1-2800=i-2800+1 by omega]
  push_cast
  linarith

lemma mesh_step (i : Nat) : (grid i:ℝ) < (grid (i+1):ℝ) := by
  exact_mod_cast grid_step i

lemma grid_zero : (grid 0:ℝ)=0 := by norm_num [grid]
lemma grid_one : (grid 100:ℝ)=1 := by norm_num [grid]
lemma grid_last : (grid 7300:ℝ)=1000 := by norm_num [grid]
lemma log_last : logUpper 7300=(690775529/100000000:ℚ) := by decide +kernel

lemma finite_M0_of_checked (checked : ∀ i : Nat, i < 7301 → allRow i=true) :
    (∫ y in (0:ℝ)..1000, |EvenKernel.transform 4 y|) ≤ (5703/1000:ℝ) := by
  have values : ∀ i ≤ 7300, |EvenKernel.transform 4 (grid i:ℝ)| ≤ (upper i:ℝ) := by
    intro i hi
    exact row_sound (allRow_parts (checked i (by omega))).1
  have h := octic_finite_quad (N := 7300) (a := fun i => (grid i:ℝ))
    (p := fun i => (upper i:ℝ)) (fun i _ => mesh_step i) values
  rw [grid_zero,grid_last] at h
  exact h.trans ((Finset.sum_le_sum (fun i hi =>
    actual_cell_cap0 (Finset.mem_range.mp hi) (checked i (by
      have hh := Finset.mem_range.mp hi; omega)))).trans sum_cap0)

lemma finite_M1_of_checked (checked : ∀ i : Nat, i < 7301 → allRow i=true) :
    (∫ y in (1:ℝ)..1000, |EvenKernel.transform 4 y| * log y) ≤ (617/100:ℝ) := by
  have values : ∀ i ≤ 7300, |EvenKernel.transform 4 (grid i:ℝ)| ≤ (upper i:ℝ) := by
    intro i hi
    exact row_sound (allRow_parts (checked i (by omega))).1
  have logs : ∀ i ≤ 7300, log (grid i:ℝ) ≤ (logUpper i:ℝ) := by
    intro i hi
    exact logRow_sound (allRow_parts (checked i (by omega))).2.1
  have mono : Monotone (fun i => (grid i:ℝ)) :=
    monotone_nat_of_le_succ (fun i => (mesh_step i).le)
  have positive : ∀ i ∈ Finset.Ico 100 7300, (1:ℝ) ≤ (grid i:ℝ) := by
    intro i hi
    rw [← grid_one]
    exact mono (Finset.mem_Ico.mp hi).1
  have h := octic_finite_log_quad (m := 100) (N := 7300) (by norm_num)
    (a := fun i => (grid i:ℝ)) (p := fun i => (upper i:ℝ))
    (l := fun i => (logUpper i:ℝ)) positive (fun i _ => mesh_step i) values logs
  rw [grid_one,grid_last] at h
  exact h.trans ((Finset.sum_le_sum (fun i hi =>
    actual_cell_cap1 (Finset.mem_Ico.mp hi).1 (Finset.mem_Ico.mp hi).2
      (checked i (by have hh := (Finset.mem_Ico.mp hi).2; omega)))).trans sum_cap1)

lemma log1000_of_checked (checked : ∀ i : Nat, i < 7301 → allRow i=true) :
    log 1000 ≤ (690775529/100000000:ℝ) := by
  have h := logRow_sound (allRow_parts (checked 7300 (by norm_num))).2.1
  rw [grid_last,log_last] at h
  simpa only [Rat.cast_div,Rat.cast_ofNat] using h

theorem actual_M0_of_checked (checked : ∀ i : Nat, i < 7301 → allRow i=true) :
    FourierMoments.M0 ≤ (143/25:ℝ) := by
  have h := M0_le_finite (finite_M0_of_checked checked)
  exact h.trans (by norm_num)

theorem actual_M1_of_checked (checked : ∀ i : Nat, i < 7301 → allRow i=true) :
    FourierMoments.M1 ≤ (23/5:ℝ) := by
  have h := M1_le_finite (finite_M1_of_checked checked) (log1000_of_checked checked)
  exact h.trans (by norm_num)

#print axioms grid_step
#print axioms finite_M0_of_checked
#print axioms finite_M1_of_checked
#print axioms actual_M0_of_checked
#print axioms actual_M1_of_checked
end RHOcticPush.Moments.Endpoint
