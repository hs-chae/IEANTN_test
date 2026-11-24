import OcticCertifiedMoments
namespace RHOcticPush.Moments.Endpoint
open Real Set MeasureTheory Finset
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

/-- Exact fixed-array totals. No endpoint/cell or program input is changed. -/
lemma total0_exact : (∑ i ∈ Finset.range 7300, cap0Numerators.get i)=5702265466890 := by
  decide +kernel
lemma total1_exact : (∑ i ∈ Finset.Ico 100 7300, cap1Numerators.get i)=6165186432541 := by
  decide +kernel

lemma strong_sum_cap0 : (∑ i ∈ Finset.range 7300, (cap0 i:ℝ)) ≤ (5702287/1000000:ℝ) := by
  unfold cap0
  push_cast
  rw [← Finset.sum_div]
  have h : (∑ i ∈ Finset.range 7300, (cap0Numerators.get i:ℝ))=5702265466890 := by
    exact_mod_cast total0_exact
  rw [h]
  norm_num

lemma strong_sum_cap1 : (∑ i ∈ Finset.Ico 100 7300, (cap1 i:ℝ)) ≤ (15413/2500:ℝ) := by
  unfold cap1
  push_cast
  rw [← Finset.sum_div]
  have h : (∑ i ∈ Finset.Ico 100 7300, (cap1Numerators.get i:ℝ))=6165186432541 := by
    exact_mod_cast total1_exact
  rw [h]
  norm_num

lemma strong_finite_M0 :
    (∫ y in (0:ℝ)..1000, |EvenKernel.transform 4 y|) ≤ (5702287/1000000:ℝ) := by
  have values : ∀ i ≤ 7300, |EvenKernel.transform 4 (grid i:ℝ)| ≤ (upper i:ℝ) := by
    intro i hi
    exact row_sound (allRow_parts (all_checked i (by omega))).1
  have h := octic_finite_quad (N := 7300) (a := fun i => (grid i:ℝ))
    (p := fun i => (upper i:ℝ)) (fun i _ => mesh_step i) values
  rw [grid_zero,grid_last] at h
  exact h.trans ((Finset.sum_le_sum (fun i hi =>
    actual_cell_cap0 (Finset.mem_range.mp hi) (all_checked i (by
      have hh := Finset.mem_range.mp hi; omega)))).trans strong_sum_cap0)

lemma strong_finite_M1 :
    (∫ y in (1:ℝ)..1000, |EvenKernel.transform 4 y| * log y) ≤ (15413/2500:ℝ) := by
  have values : ∀ i ≤ 7300, |EvenKernel.transform 4 (grid i:ℝ)| ≤ (upper i:ℝ) := by
    intro i hi
    exact row_sound (allRow_parts (all_checked i (by omega))).1
  have logs : ∀ i ≤ 7300, log (grid i:ℝ) ≤ (logUpper i:ℝ) := by
    intro i hi
    exact logRow_sound (allRow_parts (all_checked i (by omega))).2.1
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
      (all_checked i (by have hh := (Finset.mem_Ico.mp hi).2; omega)))).trans strong_sum_cap1)

theorem actual_M0_strong : FourierMoments.M0 ≤ (3574/625:ℝ) := by
  exact (M0_le_finite strong_finite_M0).trans (by norm_num)

theorem actual_M1_strong : FourierMoments.M1 ≤ (572/125:ℝ) := by
  exact (M1_le_finite strong_finite_M1 (log1000_of_checked all_checked)).trans (by norm_num)

theorem stronger_certified_moments : FourierMoments.M0 ≤ (3574/625:ℝ) ∧
    FourierMoments.M1 ≤ (572/125:ℝ) := ⟨actual_M0_strong,actual_M1_strong⟩

#print axioms total0_exact
#print axioms total1_exact
#print axioms actual_M0_strong
#print axioms actual_M1_strong
#print axioms stronger_certified_moments
end RHOcticPush.Moments.Endpoint
