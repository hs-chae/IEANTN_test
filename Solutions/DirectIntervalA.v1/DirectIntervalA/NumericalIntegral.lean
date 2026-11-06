/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import DirectIntervalA.NumericalSemantics
import DirectIntervalA.MomentOrder

namespace DirectIntervalA.Numerical
open Real Set MeasureTheory
set_option maxRecDepth 200000
set_option maxHeartbeats 0

noncomputable def edge (j : ℕ) : ℝ := 3/4+(j:ℝ)/4096
noncomputable def integrand (s : ℝ) : ℝ := exp (-(1-s)*330)*moment s (U 330)

 theorem edge_sigma (i : Fin cells) : edge i.val=sigma i := by
  simp only [edge,sigma,sigmaq]
  push_cast
  rfl

 theorem edge_succ (j : ℕ) : edge (j+1)=edge j+1/4096 := by
  simp only [edge,Nat.cast_add,Nat.cast_one]
  ring

 theorem edge_bounds (i : Fin cells) :
    3/4≤edge i.val ∧ edge (i.val+1)≤7/8 ∧ edge i.val≤edge (i.val+1) := by
  have hn : i.val<512 := i.isLt
  have hn' : (i.val:ℝ)+1≤512 := by exact_mod_cast hn
  have hz : (0 : ℝ) ≤ (i.val : ℝ) := by positivity
  rw [edge_succ]
  dsimp [edge]
  constructor
  · linarith
  constructor <;> linarith

 theorem U330_gt_one : 1<U 330 := by
  rw [U330_exp,Real.one_lt_exp_iff]
  exact u_pos

 theorem log_U330_ge_one : 1≤log (U 330) := by
  rw [log_U330]
  have hk : 0≤log ((201:ℝ)/100) := log_nonneg (by norm_num)
  dsimp [u]
  linarith

 theorem cell_subset (i : Fin cells) :
    uIcc (edge i.val) (edge (i.val+1)) ⊆ Icc (3/4:ℝ) (7/8:ℝ) := by
  rw [uIcc_of_le (edge_bounds i).2.2]
  intro s hs
  exact ⟨(edge_bounds i).1.trans hs.1,hs.2.trans (edge_bounds i).2.1⟩

 theorem integrand_continuous : ContinuousOn integrand (Icc (3/4:ℝ) (7/8:ℝ)) := by
  unfold integrand
  exact (by fun_prop : ContinuousOn (fun s:ℝ=>exp (-(1-s)*330)) _).mul
    (moment_continuousOn U330_gt_one)

 theorem cell_integrable (i : Fin cells) :
    IntervalIntegrable integrand volume (edge i.val) (edge (i.val+1)) :=
  (integrand_continuous.mono (cell_subset i)).intervalIntegrable

 theorem exponential_integral (l r : ℝ) :
    (∫s in l..r,exp (-(1-s)*330))=
      (exp (-(1-r)*330)-exp (-(1-l)*330))/330 := by
  have hd : ∀t∈uIcc l r, HasDerivAt (fun s:ℝ=>exp (-(1-s)*330)/330)
      (exp (-(1-t)*330)) t := by
    intro t _
    simpa using (((((hasDerivAt_id t).const_sub 1).neg).mul_const (330:ℝ)).exp).div_const (330:ℝ)
  have hi : IntervalIntegrable (fun s:ℝ=>exp (-(1-s)*330)) volume l r :=
    (by fun_prop : Continuous (fun s:ℝ=>exp (-(1-s)*330))).intervalIntegrable _ _
  have hh:=intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  linarith

 theorem cell_integral_bound (i : Fin cells) :
    (2*k*330*exp 66)*(∫s in edge i.val..edge (i.val+1),integrand s)≤
      weight i*moment (sigma i) (U 330) := by
  let l:=edge i.val
  let r:=edge (i.val+1)
  have hlr : l≤r := (edge_bounds i).2.2
  have hsubset:=cell_subset i
  have hmono:=moment_antitone U330_gt_one.le log_U330_ge_one
  have hleft : l∈Icc (3/4:ℝ) (7/8:ℝ) :=
    ⟨(edge_bounds i).1,hlr.trans (edge_bounds i).2.1⟩
  have hi : IntervalIntegrable (fun s:ℝ=>exp (-(1-s)*330)*moment l (U 330)) volume l r :=
    (by fun_prop : Continuous (fun s:ℝ=>exp (-(1-s)*330)*moment l (U 330))).intervalIntegrable _ _
  have hb : (∫s in l..r,integrand s)≤
      ∫s in l..r,exp (-(1-s)*330)*moment l (U 330) := by
    apply intervalIntegral.integral_mono_on hlr (cell_integrable i) hi
    intro s hs
    apply mul_le_mul_of_nonneg_left _ (exp_pos _).le
    apply hmono hleft _ hs.1
    exact ⟨hleft.1.trans hs.1,hs.2.trans (edge_bounds i).2.1⟩
  have hmul:=mul_le_mul_of_nonneg_left hb (show 0≤2*k*330*exp 66 by positivity)
  have he : (∫s in l..r,exp (-(1-s)*330)*moment l (U 330))=
      ((exp (-(1-r)*330)-exp (-(1-l)*330))/330)*moment l (U 330) := by
    rw [intervalIntegral.integral_mul_const,exponential_integral]
  rw [he] at hmul
  have hr : r=l+1/4096 := edge_succ i.val
  have hexp : exp (-(1-r)*330)=exp (-(1-l)*330)*exp ((330:ℝ)/4096) := by
    rw [←exp_add]
    congr 1
    rw [hr]
    ring
  have hprod : exp 66*exp (-(1-l)*330)=exp (66-330*(1-l)) := by
    rw [←exp_add]
    congr 1
    ring
  have hid : (2*k*330*exp 66)*
      (((exp (-(1-r)*330)-exp (-(1-l)*330))/330)*moment l (U 330))=
      weight i*moment (sigma i) (U 330) := by
    rw [hexp]
    calc
      _=(2*k*(exp 66*exp (-(1-l)*330))*(exp ((330:ℝ)/4096)-1))*moment l (U 330) := by ring
      _=_:=by rw [hprod];dsimp only [l];rw [edge_sigma i];rfl
  exact hmul.trans_eq hid

 theorem high330_le_actualMomentGrid : high 330≤actualMomentGrid := by
  have hs : (∑j∈Finset.range cells,∫s in edge j..edge (j+1),integrand s)=
      ∫s in edge 0..edge cells,integrand s := by
    apply intervalIntegral.sum_integral_adjacent_intervals
    intro j hj
    exact cell_integrable ⟨j,hj⟩
  have hedge0 : edge 0=(3/4:ℝ) := by norm_num [edge]
  have hedgeN : edge cells=(7/8:ℝ) := by norm_num [edge,cells]
  rw [hedge0,hedgeN] at hs
  have hfin : (∑i:Fin cells,∫s in edge i.val..edge (i.val+1),integrand s)=
      ∫s in (3/4:ℝ)..(7/8:ℝ),integrand s := by
    exact (Fin.sum_univ_eq_sum_range (fun j:ℕ=>∫s in edge j..edge (j+1),integrand s) cells).trans hs
  unfold high
  rw [show (330:ℝ)/5=66 by norm_num]
  change (2*k*330*exp 66)*(∫s in (3/4:ℝ)..(7/8:ℝ),integrand s)≤actualMomentGrid
  rw [←hfin,Finset.mul_sum]
  unfold actualMomentGrid
  exact Finset.sum_le_sum (fun i _=>cell_integral_bound i)

end DirectIntervalA.Numerical
#print axioms DirectIntervalA.Numerical.high330_le_actualMomentGrid
