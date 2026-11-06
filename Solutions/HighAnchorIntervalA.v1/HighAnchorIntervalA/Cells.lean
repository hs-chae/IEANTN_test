/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import HighAnchorIntervalA.Ray

namespace HighAnchorIntervalA
open Real Set MeasureTheory
set_option maxHeartbeats 0

def cells : ℕ := 256
def sigmaq (i : Fin cells) : ℚ := 3/4+(i.val:ℚ)/2048
noncomputable def sigma (i : Fin cells) : ℝ := (sigmaq i:ℝ)
noncomputable def u : ℝ := ulog 330
noncomputable def lambdaWeight : ℝ := (11/25:ℝ)*330+B
noncomputable def factorReal (s : ℝ) : ℝ := exp (p s*log k)*poly4 s u
noncomputable def weight (i : Fin cells) : ℝ :=
  (2*K*330*exp (B/8)/lambdaWeight)*exp (-lambdaWeight*(1-sigma i))*
    (exp (lambdaWeight/2048)-1)
noncomputable def correction : ℝ :=
  12*(u^2+2*u+2)*(exp (-(330:ℝ)/8)-exp (-(330:ℝ)/4))
noncomputable def actualGrid : ℝ :=
  (∑i:Fin cells,weight i*factorReal (sigma i))+correction
noncomputable def gridBudget (caps : Fin cells→ℚ) : ℝ :=
  (∑i:Fin cells,weight i*(caps i:ℝ))+correction

theorem u_pos : 0<u := ulog_pos le_rfl
theorem u_ge_one : 1≤u := by
  have hk:=log_nonneg (by norm_num [k] : (1:ℝ)≤k)
  unfold u ulog eta
  linarith
theorem lambdaWeight_pos : 0<lambdaWeight := by norm_num [lambdaWeight,B]

theorem factor_alt (s : ℝ) :
    factorReal s=exp (p s*log k+q s*log u)/b s*DirectIntervalA.factor4 s u := by
  unfold factorReal poly4
  rw [Real.rpow_def_of_pos u_pos,exp_add]
  rw [mul_comm (log u) (q s)]
  ring

theorem factor_nonneg {s : ℝ} (hs : s∈Icc (3/4:ℝ) (7/8:ℝ)) : 0≤factorReal s := by
  have hb:0<b s:=by dsimp [b,p];linarith [hs.1]
  have hf:=DirectIntervalA.factor4_nonneg hs u_pos
  rw [factor_alt]
  positivity

theorem factor_continuous : ContinuousOn factorReal (Icc (3/4:ℝ) (7/8:ℝ)) := by
  intro s hs
  have hb:b s≠0:=by dsimp [b,p];linarith [hs.1]
  have hu:u≠0:=u_pos.ne'
  have hbu:b s*u≠0:=mul_ne_zero hb hu
  unfold factorReal poly4 DirectIntervalA.factor4 DirectIntervalA.b DirectIntervalA.p DirectIntervalA.q
  dsimp [p,q,b] at *
  fun_prop (disch := first | assumption | positivity)

theorem factor_antitone : AntitoneOn factorReal (Icc (3/4:ℝ) (7/8:ℝ)) := by
  intro s hs t ht hst
  have hbs:0<b s:=by dsimp [b,p];linarith [hs.1]
  have hbt:0<b t:=by dsimp [b,p];linarith [ht.1]
  have hb:b s≤b t:=by dsimp [b,p];linarith
  have hp:p t≤p s:=by dsimp [p];linarith
  have hu : 0<u := u_pos
  have hlu:0≤log u:=log_nonneg u_ge_one
  have hlk:0≤log k:=log_nonneg (by norm_num [k])
  have hq0:0≤q t:=by dsimp [q];linarith [ht.2]
  have hq1:0≤q t-1:=by dsimp [q];linarith [ht.2]
  have hq2:0≤q t-2:=by dsimp [q];linarith [ht.2]
  have hq3:0≤q t-3:=by dsimp [q];linarith [ht.2]
  have hq:q t≤q s:=by dsimp [q];linarith
  have hqs0:0≤q s:=hq0.trans hq
  have hqs1:0≤q s-1:=by linarith
  have hqs2:0≤q s-2:=by linarith
  have hqs3:0≤q s-3:=by linarith
  have hF:DirectIntervalA.factor4 t u≤DirectIntervalA.factor4 s u:=by
    unfold DirectIntervalA.factor4 DirectIntervalA.q DirectIntervalA.b DirectIntervalA.p
    dsimp [q,b,p] at *
    gcongr <;> first | positivity | linarith
  have hex:exp (p t*log k+q t*log u)≤exp (p s*log k+q s*log u):=by
    apply exp_le_exp.mpr
    nlinarith
  have hdiv:exp (p t*log k+q t*log u)/b t≤exp (p s*log k+q s*log u)/b s:=
    div_le_div₀ (exp_pos _).le hex hbs hb
  rw [factor_alt,factor_alt]
  exact mul_le_mul hdiv hF (DirectIntervalA.factor4_nonneg ht u_pos) (by positivity)

theorem weight_nonneg (i : Fin cells) : 0≤weight i := by
  have hlambda := lambdaWeight_pos
  have hd:0≤exp (lambdaWeight/2048)-1:=sub_nonneg.mpr (one_le_exp (by linarith [lambdaWeight_pos]))
  unfold weight K
  positivity

noncomputable def kernel (s : ℝ) : ℝ := exp (-lambdaWeight*(1-s))*factorReal s
noncomputable def edge (j : ℕ) : ℝ := 3/4+(j:ℝ)/2048
noncomputable def factoredIntegral : ℝ :=
  (2*K*330*exp (B/8))*(∫s in (3/4:ℝ)..(7/8:ℝ),kernel s)+correction

theorem integrand330_eq {s : ℝ} (hs : s∈Icc (3/4:ℝ) (7/8:ℝ)) :
    integrand 330 s=(2*K*330*exp (B/8))*kernel s+
      (12*330*(u^2+2*u+2))*exp (-(1-s)*330) := by
  have hu:u≠0:=u_pos.ne'
  have hb:b s≠0:=by dsimp [b,p];linarith [hs.1]
  have he:exp (B*(s-7/8))*exp (-rate s*330)=
      exp (B/8)*exp (-lambdaWeight*(1-s)):=by
    rw [←exp_add,←exp_add]
    congr 1
    unfold rate lambdaWeight
    ring
  rw [integrand_eq s 330 hs le_rfl]
  calc
    _ = (2*K*330)*(exp (B*(s-7/8))*exp (-rate s*330))*
        (exp (p s*log k)*u^(q s)/b s*DirectIntervalA.factor4 s u)+
        (12*330*(u^2+2*u+2))*exp (-(1-s)*330) := by
      unfold mainRay correctionRay coeff DirectIntervalA.factor2
      change _ = _
      rw [show ulog 330=u by rfl]
      field_simp
      <;> ring
    _ = _ := by rw [he];unfold kernel factorReal poly4;ring

theorem kernel_continuous : ContinuousOn kernel (Icc (3/4:ℝ) (7/8:ℝ)) := by
  unfold kernel
  exact (by fun_prop : ContinuousOn (fun s:ℝ=>exp (-lambdaWeight*(1-s))) _).mul factor_continuous

theorem exponential_integral (a l r : ℝ) (ha : a≠0) :
    (∫s in l..r,exp (-a*(1-s)))=(exp (-a*(1-r))-exp (-a*(1-l)))/a := by
  have hd:∀t∈uIcc l r,HasDerivAt (fun s:ℝ=>exp (-a*(1-s))/a) (exp (-a*(1-t))) t:=by
    intro t _
    simpa [ha,mul_comm] using
      (((((hasDerivAt_id t).const_sub 1).mul_const (-a)).exp).div_const a)
  have hi:IntervalIntegrable (fun s:ℝ=>exp (-a*(1-s))) volume l r:=
    (by fun_prop : Continuous (fun s:ℝ=>exp (-a*(1-s)))).intervalIntegrable _ _
  have hh:=intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  rw [hh]
  ring

theorem high330_eq_factored : high 330=factoredIntegral := by
  have hi1:IntervalIntegrable kernel volume (3/4:ℝ) (7/8:ℝ):=by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (by norm_num : (3/4:ℝ)≤7/8)]
    exact kernel_continuous
  have hi2:IntervalIntegrable (fun s:ℝ=>exp (-(1-s)*330)) volume (3/4:ℝ) (7/8:ℝ):=
    (by fun_prop : Continuous (fun s:ℝ=>exp (-(1-s)*330))).intervalIntegrable _ _
  rw [high_as_integral]
  have he:(∫s in (3/4:ℝ)..(7/8:ℝ),integrand 330 s)=
      ∫s in (3/4:ℝ)..(7/8:ℝ),(2*K*330*exp (B/8))*kernel s+
        (12*330*(u^2+2*u+2))*exp (-(1-s)*330):=by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le (by norm_num : (3/4:ℝ)≤7/8)] at hs
    exact integrand330_eq hs
  rw [he,intervalIntegral.integral_add (hi1.const_mul _) (hi2.const_mul _),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]
  have hI:(∫s in (3/4:ℝ)..(7/8:ℝ),exp (-(1-s)*330))=
      (exp (-(330:ℝ)/8)-exp (-(330:ℝ)/4))/330:=by
    calc
      _ = ∫s in (3/4:ℝ)..(7/8:ℝ),exp (-(330:ℝ)*(1-s)) := by
        apply intervalIntegral.integral_congr
        intro s _
        congr 1
        ring
      _ = (exp (-(330:ℝ)*(1-7/8))-exp (-(330:ℝ)*(1-3/4)))/330 :=
        exponential_integral 330 (3/4) (7/8) (by norm_num)
      _ = _ := by norm_num
  rw [hI]
  unfold factoredIntegral correction
  ring

theorem edge_sigma (i : Fin cells) : edge i.val=sigma i := by
  simp only [edge,sigma,sigmaq]
  push_cast
  rfl
theorem edge_succ (j : ℕ) : edge (j+1)=edge j+1/2048 := by
  simp only [edge,Nat.cast_add,Nat.cast_one]
  ring
theorem edge_bounds (i : Fin cells) :
    3/4≤edge i.val ∧ edge (i.val+1)≤7/8 ∧ edge i.val≤edge (i.val+1) := by
  have hn:i.val<256:=i.isLt
  have hn':(i.val:ℝ)+1≤256:=by exact_mod_cast hn
  have hz:(0:ℝ)≤(i.val:ℝ):=by positivity
  rw [edge_succ]
  dsimp [edge]
  constructor
  · linarith
  constructor <;> linarith
theorem cell_subset (i : Fin cells) :
    uIcc (edge i.val) (edge (i.val+1))⊆Icc (3/4:ℝ) (7/8:ℝ) := by
  rw [uIcc_of_le (edge_bounds i).2.2]
  intro s hs
  exact ⟨(edge_bounds i).1.trans hs.1,hs.2.trans (edge_bounds i).2.1⟩
theorem cell_integrable (i : Fin cells) :
    IntervalIntegrable kernel volume (edge i.val) (edge (i.val+1)) :=
  (kernel_continuous.mono (cell_subset i)).intervalIntegrable

theorem cell_integral_bound (i : Fin cells) :
    (2*K*330*exp (B/8))*(∫s in edge i.val..edge (i.val+1),kernel s)≤weight i*factorReal (sigma i) := by
  let l:=edge i.val
  let r:=edge (i.val+1)
  have hlr:l≤r:=(edge_bounds i).2.2
  have hleft:l∈Icc (3/4:ℝ) (7/8:ℝ):=⟨(edge_bounds i).1,hlr.trans (edge_bounds i).2.1⟩
  have hi:IntervalIntegrable (fun s:ℝ=>exp (-lambdaWeight*(1-s))*factorReal l) volume l r:=
    (by fun_prop : Continuous (fun s:ℝ=>exp (-lambdaWeight*(1-s))*factorReal l)).intervalIntegrable _ _
  have hb:(∫s in l..r,kernel s)≤∫s in l..r,exp (-lambdaWeight*(1-s))*factorReal l:=by
    apply intervalIntegral.integral_mono_on hlr (cell_integrable i) hi
    intro s hs
    apply mul_le_mul_of_nonneg_left _ (exp_pos _).le
    exact factor_antitone hleft ⟨hleft.1.trans hs.1,hs.2.trans (edge_bounds i).2.1⟩ hs.1
  have hm:=mul_le_mul_of_nonneg_left hb (show 0≤2*K*330*exp (B/8) by norm_num [K];positivity)
  have he:(∫s in l..r,exp (-lambdaWeight*(1-s))*factorReal l)=
      ((exp (-lambdaWeight*(1-r))-exp (-lambdaWeight*(1-l)))/lambdaWeight)*factorReal l:=by
    rw [intervalIntegral.integral_mul_const,exponential_integral _ _ _ lambdaWeight_pos.ne']
  rw [he] at hm
  have hr:r=l+1/2048:=edge_succ i.val
  have hx:exp (-lambdaWeight*(1-r))=exp (-lambdaWeight*(1-l))*exp (lambdaWeight/2048):=by
    rw [←exp_add]
    congr 1
    rw [hr]
    ring
  have hid:(2*K*330*exp (B/8))*
      (((exp (-lambdaWeight*(1-r))-exp (-lambdaWeight*(1-l)))/lambdaWeight)*factorReal l)=
      weight i*factorReal (sigma i):=by
    rw [hx]
    dsimp only [l]
    rw [edge_sigma i]
    unfold weight
    ring
  exact hm.trans_eq hid

theorem high330_le_actualGrid : high 330≤actualGrid := by
  have hs:(∑j∈Finset.range cells,∫s in edge j..edge (j+1),kernel s)=
      ∫s in edge 0..edge cells,kernel s:=by
    apply intervalIntegral.sum_integral_adjacent_intervals
    intro j hj
    exact cell_integrable ⟨j,hj⟩
  have h0:edge 0=(3/4:ℝ):=by norm_num [edge]
  have hN:edge cells=(7/8:ℝ):=by norm_num [edge,cells]
  rw [h0,hN] at hs
  have hfin:(∑i:Fin cells,∫s in edge i.val..edge (i.val+1),kernel s)=
      ∫s in (3/4:ℝ)..(7/8:ℝ),kernel s:=
    (Fin.sum_univ_eq_sum_range (fun j:ℕ=>∫s in edge j..edge (j+1),kernel s) cells).trans hs
  rw [high330_eq_factored]
  unfold factoredIntegral actualGrid
  apply add_le_add _ le_rfl
  rw [←hfin,Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _=>cell_integral_bound i)

theorem high330_le_gridBudget (caps : Fin cells→ℚ)
    (hcaps : ∀i,factorReal (sigma i)≤(caps i:ℝ)) : high 330≤gridBudget caps := by
  apply high330_le_actualGrid.trans
  unfold actualGrid gridBudget
  apply add_le_add _ le_rfl
  exact Finset.sum_le_sum (fun i _=>mul_le_mul_of_nonneg_left (hcaps i) (weight_nonneg i))

end HighAnchorIntervalA
#print axioms HighAnchorIntervalA.high330_le_gridBudget
