/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import DirectIntervalA.EvolvedSemantics

namespace DirectIntervalA.Evolved
open Real Set MeasureTheory
set_option maxRecDepth 200000
set_option maxHeartbeats 0

noncomputable def kernel (s : ℝ) : ℝ := exp (-154*(1-s))*factorReal s
noncomputable def edge (j : ℕ) : ℝ := 3/4+(j:ℝ)/512
noncomputable def factoredIntegral : ℝ :=
  (2*(1959/200:ℝ)*330)*(∫s in (3/4:ℝ)..(7/8:ℝ),kernel s)+correction

 theorem factor_alt (s : ℝ) : factorReal s=
    exp (p s*log k)*Numerical.u^(q s)/b s*factor4 s Numerical.u := by
  have hb : 1-b s=p s := by unfold b;ring
  unfold factorReal
  rw [hb,exp_add,Real.rpow_def_of_pos Numerical.u_pos]
  rw [mul_comm (log Numerical.u) (q s)]

 theorem integrand330_eq {s : ℝ} (hs : s∈Icc (3/4:ℝ) (7/8:ℝ)) :
    DirectIntervalA.integrand 330 s=(2*(1959/200:ℝ)*330)*kernel s+
      (2*(893/200:ℝ)*330*(Numerical.u^2+2*Numerical.u+2))*exp (-(1-s)*330) := by
  rw [DirectIntervalA.integrand_eq s 330 hs le_rfl]
  have hu : Numerical.u≠0 := Numerical.u_pos.ne'
  have hb : b s≠0 := by unfold b p;linarith [hs.1]
  have hulog : ulog 330=Numerical.u := by norm_num [ulog,Numerical.u,k]
  have he : -rate s*330= -154*(1-s) := by unfold rate;ring
  unfold mainRay correctionRay kernel
  rw [hulog,he,factor_alt]
  unfold factor2
  field_simp
  <;> ring

 theorem kernel_continuous : ContinuousOn kernel (Icc (3/4:ℝ) (7/8:ℝ)) := by
  unfold kernel
  exact (by fun_prop : ContinuousOn (fun s:ℝ=>exp (-154*(1-s))) _).mul factor_continuous

 theorem high330_eq_factored : high 330=factoredIntegral := by
  have hi1 : IntervalIntegrable kernel volume (3/4:ℝ) (7/8:ℝ) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (by norm_num : (3/4:ℝ)≤7/8)]
    exact kernel_continuous
  have hi2 : IntervalIntegrable (fun s:ℝ=>exp (-(1-s)*330)) volume (3/4:ℝ) (7/8:ℝ) :=
    (by fun_prop : Continuous (fun s:ℝ=>exp (-(1-s)*330))).intervalIntegrable _ _
  rw [high_as_integral]
  have he : (∫s in (3/4:ℝ)..(7/8:ℝ),DirectIntervalA.integrand 330 s)=
      ∫s in (3/4:ℝ)..(7/8:ℝ),
        (2*(1959/200:ℝ)*330)*kernel s+
          (2*(893/200:ℝ)*330*(Numerical.u^2+2*Numerical.u+2))*exp (-(1-s)*330) := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le (by norm_num : (3/4:ℝ)≤7/8)] at hs
    exact integrand330_eq hs
  rw [he,intervalIntegral.integral_add (hi1.const_mul _) (hi2.const_mul _)]
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    Numerical.exponential_integral]
  unfold factoredIntegral correction
  norm_num
  ring

 theorem edge_sigma (i : Fin cells) : edge i.val=sigma i := by
  simp only [edge,sigma,sigmaq]
  push_cast
  rfl

 theorem edge_succ (j : ℕ) : edge (j+1)=edge j+1/512 := by
  simp only [edge,Nat.cast_add,Nat.cast_one]
  ring

 theorem edge_bounds (i : Fin cells) :
    3/4≤edge i.val ∧ edge (i.val+1)≤7/8 ∧ edge i.val≤edge (i.val+1) := by
  have hn : i.val<64 := i.isLt
  have hn' : (i.val:ℝ)+1≤64 := by exact_mod_cast hn
  have hz : (0:ℝ) ≤ (i.val:ℝ) := by positivity
  rw [edge_succ]
  dsimp [edge]
  constructor
  · linarith
  constructor <;> linarith

 theorem cell_subset (i : Fin cells) :
    uIcc (edge i.val) (edge (i.val+1)) ⊆ Icc (3/4:ℝ) (7/8:ℝ) := by
  rw [uIcc_of_le (edge_bounds i).2.2]
  intro s hs
  exact ⟨(edge_bounds i).1.trans hs.1,hs.2.trans (edge_bounds i).2.1⟩

 theorem cell_integrable (i : Fin cells) :
    IntervalIntegrable kernel volume (edge i.val) (edge (i.val+1)) :=
  (kernel_continuous.mono (cell_subset i)).intervalIntegrable

 theorem exponential_integral (l r : ℝ) :
    (∫s in l..r,exp (-154*(1-s)))=
      (exp (-154*(1-r))-exp (-154*(1-l)))/154 := by
  have hd : ∀t∈uIcc l r, HasDerivAt (fun s:ℝ=>exp (-154*(1-s))/154)
      (exp (-154*(1-t))) t := by
    intro t _
    simpa [mul_comm] using (((((hasDerivAt_id t).const_sub 1).mul_const (-154:ℝ)).exp).div_const (154:ℝ))
  have hi : IntervalIntegrable (fun s:ℝ=>exp (-154*(1-s))) volume l r :=
    (by fun_prop : Continuous (fun s:ℝ=>exp (-154*(1-s)))).intervalIntegrable _ _
  have hh:=intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  linarith

 theorem cell_integral_bound (i : Fin cells) :
    (2*(1959/200:ℝ)*330)*(∫s in edge i.val..edge (i.val+1),kernel s)≤
      weight i*factorReal (sigma i) := by
  let l:=edge i.val
  let r:=edge (i.val+1)
  have hlr : l≤r := (edge_bounds i).2.2
  have hleft : l∈Icc (3/4:ℝ) (7/8:ℝ) :=
    ⟨(edge_bounds i).1,hlr.trans (edge_bounds i).2.1⟩
  have hi : IntervalIntegrable (fun s:ℝ=>exp (-154*(1-s))*factorReal l) volume l r :=
    (by fun_prop : Continuous (fun s:ℝ=>exp (-154*(1-s))*factorReal l)).intervalIntegrable _ _
  have hb : (∫s in l..r,kernel s)≤∫s in l..r,exp (-154*(1-s))*factorReal l := by
    apply intervalIntegral.integral_mono_on hlr (cell_integrable i) hi
    intro s hs
    apply mul_le_mul_of_nonneg_left _ (exp_pos _).le
    exact factor_antitone hleft ⟨hleft.1.trans hs.1,hs.2.trans (edge_bounds i).2.1⟩ hs.1
  have hmul:=mul_le_mul_of_nonneg_left hb (show 0≤2*(1959/200:ℝ)*330 by positivity)
  have he : (∫s in l..r,exp (-154*(1-s))*factorReal l)=
      ((exp (-154*(1-r))-exp (-154*(1-l)))/154)*factorReal l := by
    rw [intervalIntegral.integral_mul_const,exponential_integral]
  rw [he] at hmul
  have hr : r=l+1/512 := edge_succ i.val
  have hexp : exp (-154*(1-r))=exp (-154*(1-l))*exp ((154:ℝ)/512) := by
    rw [←exp_add]
    congr 1
    rw [hr]
    ring
  have hid : (2*(1959/200:ℝ)*330)*
      (((exp (-154*(1-r))-exp (-154*(1-l)))/154)*factorReal l)=
      weight i*factorReal (sigma i) := by
    rw [hexp]
    dsimp only [l]
    rw [edge_sigma i]
    unfold weight
    ring
  exact hmul.trans_eq hid

 theorem high330_le_actualGrid : high 330≤actualGrid := by
  have hs : (∑j∈Finset.range cells,∫s in edge j..edge (j+1),kernel s)=
      ∫s in edge 0..edge cells,kernel s := by
    apply intervalIntegral.sum_integral_adjacent_intervals
    intro j hj
    exact cell_integrable ⟨j,hj⟩
  have hedge0 : edge 0=(3/4:ℝ) := by norm_num [edge]
  have hedgeN : edge cells=(7/8:ℝ) := by norm_num [edge,cells]
  rw [hedge0,hedgeN] at hs
  have hfin : (∑i:Fin cells,∫s in edge i.val..edge (i.val+1),kernel s)=
      ∫s in (3/4:ℝ)..(7/8:ℝ),kernel s :=
    (Fin.sum_univ_eq_sum_range (fun j:ℕ=>∫s in edge j..edge (j+1),kernel s) cells).trans hs
  rw [high330_eq_factored]
  unfold factoredIntegral actualGrid
  apply add_le_add _ le_rfl
  rw [←hfin,Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _=>cell_integral_bound i)

end DirectIntervalA.Evolved
#print axioms DirectIntervalA.Evolved.high330_le_actualGrid
