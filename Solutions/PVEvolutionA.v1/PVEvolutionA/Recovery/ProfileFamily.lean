/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import PVEvolutionA.Recovery.ProfileRun
import PVEvolutionA.Recovery.ProfileSource
import WinnerDensityA.HeightPrimary

namespace PVEvolutionA.Recovery.Profiles
open Real Set MeasureTheory WinnerOriginalScalars
set_option maxHeartbeats 0

def index (j : ℕ) : Fin 128 := ⟨min j 127,by omega⟩
noncomputable def anchor (j : ℕ) : ℝ := Profile.anchor (row (index j))
noncomputable def coeff (sigma : ℝ) (j : ℕ) : ℝ :=
  ((row (index j)).K:ℝ)*exp ((slope (index j):ℝ)*(sigma-7/8))

theorem index_of_le {j : ℕ} (hj : j≤127) : index j=⟨j,by omega⟩ := by
  apply Fin.ext
  exact min_eq_left hj

theorem anchor_formula (j : ℕ) : anchor j=height*exp (((min j 127:ℕ):ℝ)/8) := by
  unfold anchor Profile.anchor
  rw [shifts]
  push_cast
  simp [index]

theorem anchor_zero : anchor 0=WinnerDensityA.H := by
  rw [anchor_formula]
  norm_num [height,WinnerDensityA.H]

theorem anchor_mono : Monotone anchor := by
  intro i j hij
  rw [anchor_formula,anchor_formula]
  apply mul_le_mul_of_nonneg_left _ (by norm_num [height])
  apply exp_le_exp.mpr
  have hh : min i 127≤min j 127 := min_le_min_right 127 hij
  exact div_le_div_of_nonneg_right (by exact_mod_cast hh) (by norm_num)

theorem height_lt_anchor {j : ℕ} (hj : j<127) : WinnerDensityA.H<anchor (j+1) := by
  rw [anchor_formula]
  have hp : (0:ℝ)<((min (j+1) 127:ℕ):ℝ) := by exact_mod_cast (by omega : 0<min (j+1) 127)
  have he : 1<exp (((min (j+1) 127:ℕ):ℝ)/8) := one_lt_exp_iff.mpr (by positivity)
  norm_num [WinnerDensityA.H,height] at *
  linarith

theorem row_K_pos (i : Fin 128) : (0:ℝ)<(row i).K := by
  have h := arithmetic i
  exact_mod_cast h.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem coeff_nonneg (sigma : ℝ) (j : ℕ) : 0≤coeff sigma j := by
  unfold coeff
  exact mul_nonneg (row_K_pos _).le (exp_pos _).le

theorem coeff_antitone {sigma : ℝ} (hs : sigma≤7/8) : Antitone (coeff sigma) := by
  apply antitone_nat_of_succ_le
  intro j
  by_cases hj : j<127
  · have hcurr := index_of_le (j:=j) (by omega)
    have hnext := index_of_le (j:=j+1) (by omega)
    obtain ⟨hK,hB⟩ := ordered ⟨j,hj⟩
    have hk : ((row ⟨j+1,by omega⟩).K:ℝ)≤(row ⟨j,by omega⟩).K := by exact_mod_cast hK
    have hb : (slope ⟨j,by omega⟩:ℝ)≤slope ⟨j+1,by omega⟩ := by exact_mod_cast hB
    have he : exp ((slope ⟨j+1,by omega⟩:ℝ)*(sigma-7/8))≤
        exp ((slope ⟨j,by omega⟩:ℝ)*(sigma-7/8)) := by
      apply exp_le_exp.mpr
      exact mul_le_mul_of_nonpos_right hb (sub_nonpos.mpr hs)
    unfold coeff
    rw [hcurr,hnext]
    exact mul_le_mul hk he (exp_pos _).le (row_K_pos _).le
  · have h1 : index j=⟨127,by decide⟩ := by apply Fin.ext;dsimp [index];omega
    have h2 : index (j+1)=⟨127,by decide⟩ := by apply Fin.ext;dsimp [index];omega
    simp only [coeff,h1,h2,le_refl]

theorem count_closed
    (accepted : ∀j:Fin 18,WinnerProgramA.acceptUpper (GaussianBasis.output j)
      [(GaussianBasis.spec j).cap]=true)
    (h : WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH : IEANTN.RiemannHypothesisUpTo height)
    (j : ℕ) {sigma T : ℝ} (hs : (3/4:ℝ)≤sigma) (hs' : sigma≤7/8)
    (hT : anchor j≤T) :
    IEANTN.zetaZeroesSum (Ioo sigma 1) (Ioc 0 T) (fun _↦(1:ℝ))≤
      WinnerDensityA.poly (coeff sigma j) 6 sigma T := by
  exact Profile.count_closed (row (index j)) (slope (index j))
    (arithmetic _) (scalar_checks _) accepted (h.toNewInputs (by norm_num)) hRH hs hs' hT

#print axioms anchor_mono
#print axioms coeff_antitone
#print axioms count_closed
end PVEvolutionA.Recovery.Profiles
