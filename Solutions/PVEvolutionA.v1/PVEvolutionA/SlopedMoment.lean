/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import WinnerDensityA.HeightPrimary
import WinnerDensityA.StepMoment
import WinnerDensityA.Moment
namespace PVEvolutionA.SlopedMoment
open Real Set MeasureTheory Filter Topology CH2QRH
open WinnerHeightProfiles
open WinnerDensityA.Piecewise
set_option maxHeartbeats 0
def slope (j:Fin 4) : ℚ := match j.val with
  | 0 => 54281/10000
  | 1 => 54364/10000
  | 2 => 54441/10000
  | _ => 54580/10000

theorem slope_lower (j:Fin 4) : ((slope j:ℚ):ℝ)≤
    2*log ((row j).V/(row j).U:ℝ)+4*(3599/10000)*
      WinnerDensitySource.interpolationPhi (3599/10000) (row j).U (row j).V := by
  rw [←WinnerHeightProfiles.b_semantics]
  fin_cases j <;> exact WinnerOriginalScalars.closed_lower _ _ (by native_decide)

noncomputable def coeff (j:Fin 4) (sigma:ℝ) : ℝ :=
  ((row j).K:ℝ)*exp ((slope j:ℝ)*(sigma-7/8))
noncomputable def p (sigma:ℝ) : ℝ :=8*(1-sigma)/3
noncomputable def q (sigma:ℝ) : ℝ :=5-2*sigma
noncomputable def step (sigma t:ℝ) : ℝ :=
  stepMajorant (p sigma) (q sigma) (coeff 0 sigma) (coeff 1 sigma)
    (coeff 2 sigma) (coeff 3 sigma) 6 (anchor 1) (anchor 2) (anchor 3) t
noncomputable def moment (sigma:ℝ) : ℝ :=
  coeff 0 sigma*upper (p sigma) (q sigma) WinnerDensityA.H
  -(coeff 0 sigma-coeff 1 sigma)*lower (p sigma) (q sigma) (anchor 1)
  -(coeff 1 sigma-coeff 2 sigma)*lower (p sigma) (q sigma) (anchor 2)
  -(coeff 2 sigma-coeff 3 sigma)*lower (p sigma) (q sigma) (anchor 3)
  +6*((log WinnerDensityA.H^(2:ℕ)+2*log WinnerDensityA.H+2)/WinnerDensityA.H)
noncomputable def envelope (sigma tau:ℝ) : ℝ :=
  2*moment sigma+4*Real.pi*(WinnerDensityA.poly (coeff 0 sigma) 6 sigma (exp tau)/exp tau)

theorem coeff_nonneg (j:Fin 4) (sigma:ℝ) : 0≤coeff j sigma := by
  have h:0≤((row j).K:ℝ):=by fin_cases j <;> norm_num [row]
  exact mul_nonneg h (exp_pos _).le

theorem coeff_order (sigma:ℝ) (hs:sigma≤7/8) : coeff 1 sigma≤coeff 0 sigma ∧
    coeff 2 sigma≤coeff 1 sigma ∧ coeff 3 sigma≤coeff 2 sigma := by
  have he01 : exp ((slope 1:ℝ)*(sigma-7/8))≤exp ((slope 0:ℝ)*(sigma-7/8)) :=
    exp_le_exp.mpr (by norm_num [slope]; nlinarith)
  have he12 : exp ((slope 2:ℝ)*(sigma-7/8))≤exp ((slope 1:ℝ)*(sigma-7/8)) :=
    exp_le_exp.mpr (by norm_num [slope]; nlinarith)
  have he23 : exp ((slope 3:ℝ)*(sigma-7/8))≤exp ((slope 2:ℝ)*(sigma-7/8)) :=
    exp_le_exp.mpr (by norm_num [slope]; nlinarith)
  have hp0 := (exp_pos ((slope 0:ℝ)*(sigma-7/8))).le
  have hp1 := (exp_pos ((slope 1:ℝ)*(sigma-7/8))).le
  have hp2 := (exp_pos ((slope 2:ℝ)*(sigma-7/8))).le
  norm_num [coeff,row]
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem profile_count (h:WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH:IEANTN.RiemannHypothesisUpTo WinnerOriginalScalars.height) (j:Fin 4)
    {sigma T:ℝ} (hs:(3/4:ℝ)≤sigma) (hs':sigma≤7/8) (hT:anchor j≤T) :
    IEANTN.zetaN' sigma T≤coeff j sigma*T^(8*(1-sigma)/3)*log T^(5-2*sigma)+6*log T^(2:ℕ) := by
  have hh:=WinnerNewHeightSource.count_at_anchor (h.toNewInputs (by norm_num))
    (by norm_num : (34/100:ℝ)≤3681/10000) (by norm_num : (3681/10000:ℝ)≤2/5)
    (by norm_num : (0:ℝ)<3599/10000) (height_le_anchor j) hT (row_U_pos j) (row_V_pos j)
    (WinnerNewHeightSource.profileCertificate j) (right_v_upper j)
    (coefficient_upper j) (slope_lower j) hRH hs hs'
  simpa only [coeff,show -((slope j:ℚ):ℝ)*(7/8-sigma)=(slope j:ℝ)*(sigma-7/8) by ring] using hh

theorem anchor_zero : anchor 0=WinnerDensityA.H := by
  norm_num [anchor,row,WinnerOriginalScalars.height,WinnerDensityA.H]

theorem anchor_order : WinnerDensityA.H<anchor 1 ∧ anchor 1≤anchor 2 ∧ anchor 2≤anchor 3 := by
  have hH:0<WinnerOriginalScalars.height:=by norm_num [WinnerOriginalScalars.height]
  have he1:1<exp (1:ℝ):=by exact one_lt_exp_iff.mpr (by norm_num)
  have he12:exp (1:ℝ)≤exp 2:=exp_le_exp.mpr (by norm_num)
  have he24:exp (2:ℝ)≤exp 4:=exp_le_exp.mpr (by norm_num)
  norm_num [anchor,row]
  exact ⟨by change WinnerOriginalScalars.height<WinnerOriginalScalars.height*exp 1; nlinarith,
    mul_le_mul_of_nonneg_left he12 hH.le,mul_le_mul_of_nonneg_left he24 hH.le⟩

theorem profile_count_closed
    (h:WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH:IEANTN.RiemannHypothesisUpTo WinnerOriginalScalars.height) (j:Fin 4)
    {sigma T:ℝ} (hs:(3/4:ℝ)≤sigma) (hs':sigma≤7/8) (hT:anchor j≤T) :
    IEANTN.zetaZeroesSum (Ioo sigma 1) (Ioc 0 T) (fun _↦(1:ℝ))≤
      WinnerDensityA.poly (coeff j sigma) 6 sigma T := by
  have hT1:1<T:=(anchor_gt_one j).trans_le hT
  have hlim: Tendsto (WinnerDensityA.poly (coeff j sigma) 6 sigma) (𝓝[>] T)
      (𝓝 (WinnerDensityA.poly (coeff j sigma) 6 sigma T)):=
    (WinnerDensityA.poly_continuous hT1).tendsto.mono_left nhdsWithin_le_nhds
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with u hu
  have hc:=profile_count h hRH j hs hs' (hT.trans hu.le)
  exact (density_closed_le_open (by linarith) hu).trans (by simpa only [WinnerDensityA.poly] using hc)

theorem step_count_closed
    (h:WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH:IEANTN.RiemannHypothesisUpTo WinnerOriginalScalars.height)
    {sigma T:ℝ} (hs:(3/4:ℝ)≤sigma) (hs':sigma≤7/8) (hT:WinnerDensityA.H≤T) :
    IEANTN.zetaZeroesSum (Ioo sigma 1) (Ioc 0 T) (fun _↦(1:ℝ))≤step sigma T := by
  unfold step stepMajorant coefficient
  split_ifs with h3 h2 h1
  · exact profile_count_closed h hRH 3 hs hs' h3
  · exact profile_count_closed h hRH 2 hs hs' h2
  · exact profile_count_closed h hRH 1 hs hs' h1
  · exact profile_count_closed h hRH 0 hs hs' (by simpa only [anchor_zero] using hT)

/-- A fixed finite zero rectangle is contained in the actual closed count at
any later partial-summation argument; no monotonicity of the majorant is used. -/
theorem partial_closed_le {sigma T u:ℝ} :
    (∑rho∈(finite_zero_rectangle (Ioo sigma 1) (T:=T)).toFinset,
      if rho.im≤u then (IEANTN.zetaOrder rho:ℝ) else 0)≤
    IEANTN.zetaZeroesSum (Ioo sigma 1) (Ioc 0 u) (fun _↦(1:ℝ)) := by
  classical
  let S:=(finite_zero_rectangle (Ioo sigma 1) (T:=T)).toFinset
  have hu:=finite_zero_rectangle (Ioo sigma 1) (T:=u)
  rw [rectangle_sum_eq hu]
  simp only [one_mul]
  change (∑rho∈S,if rho.im≤u then (IEANTN.zetaOrder rho:ℝ) else 0)≤_
  rw [←Finset.sum_filter]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro rho hrho
    obtain ⟨hS,hcut⟩:=Finset.mem_filter.mp hrho
    have hz:rho∈IEANTN.zetaZeroesIn (Ioo sigma 1) (Ioc 0 T):=
      (Set.Finite.mem_toFinset _).mp hS
    exact (Set.Finite.mem_toFinset hu).mpr ⟨hz.1,⟨hz.2.1.1,hcut⟩,hz.2.2⟩
  · intro rho hrho _
    have hz:=(Set.Finite.mem_toFinset hu).mp hrho
    exact CH2Section7Z.zetaOrder_nonneg_of_mem (J:=Ioo 0 (u+1)) Set.Ioo_subset_Ioi_self
      ⟨trivial,⟨hz.2.1.1,lt_of_le_of_lt hz.2.1.2 (by linarith)⟩,hz.2.2⟩

theorem reciprocal_moment
    (h:WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH:IEANTN.RiemannHypothesisUpTo WinnerOriginalScalars.height)
    {sigma T:ℝ} (hs:(3/4:ℝ)≤sigma) (hs':sigma≤7/8) (hT:WinnerDensityA.H≤T) :
    IEANTN.zetaZeroesSum (Ioo sigma 1) (Ioc 0 T) (fun rho↦1/rho.im)≤moment sigma := by
  classical
  have hA:1<WinnerDensityA.H:=by norm_num [WinnerDensityA.H]
  have hl:1≤log WinnerDensityA.H:=le_trans (by norm_num) WinnerOriginalScalars.source_log_lower
  have hp:0≤p sigma:=by unfold p; linarith
  have hp':p sigma<1:=by unfold p; linarith
  have hq:3≤q sigma:=by unfold q; linarith
  have hq':q sigma≤4:=by unfold q; linarith
  obtain ⟨ha,h12,h23⟩:=anchor_order
  obtain ⟨hc1,hc2,hc3⟩:=coeff_order sigma hs'
  have hi:IntegrableOn (fun u=>step sigma u/u^2) (Ioi WinnerDensityA.H):=
    step_integrable hA hl hp hp' hq' h12 h23
  have hb:Tendsto (fun u=>step sigma u/u) atTop (𝓝 0):=step_boundary_zero hp'
  have hfin:=finite_zero_rectangle (Ioo sigma 1) (T:=T)
  let S:=hfin.toFinset
  have hgamma:∀rho∈S,WinnerDensityA.H<rho.im ∧ rho.im≤T:=by
    intro rho hrho
    have hz:=(Set.Finite.mem_toFinset hfin).mp hrho
    refine ⟨?_,hz.2.1.2⟩
    by_contra he
    have hzlow:rho∈IEANTN.zetaZeroesIn (Ioo (1/2) 1) (Icc 0 WinnerOriginalScalars.height):=
      ⟨⟨by linarith [hz.1.1],hz.1.2⟩,⟨hz.2.1.1.le,not_lt.mp he⟩,hz.2.2⟩
    exact hRH.false ⟨rho,hzlow⟩
  have hc:∀u:ℝ,WinnerDensityA.H≤u→
      (∑rho∈S,if rho.im≤u then (IEANTN.zetaOrder rho:ℝ) else 0)≤step sigma u:=by
    intro u hu
    exact partial_closed_le.trans (step_count_closed h hRH hs hs' hu)
  have hg:=finite_reciprocal_global S Complex.im (fun rho↦(IEANTN.zetaOrder rho:ℝ))
    (by linarith) hT hgamma (step sigma) hi hb hc
  have hu:=step_integral_upper hA hl hp hp' hq hq' ha h12 h23
    (coeff_nonneg 0 sigma) hc1 hc2 hc3 (by norm_num : (0:ℝ)≤6)
  rw [rectangle_sum_eq hfin]
  have hh:IEANTN.zetaZeroesSum (Ioo sigma 1) (Ioc 0 T) (fun rho↦1/rho.im)≤
      ∫u in Ioi WinnerDensityA.H,step sigma u/u^2 := by
    rw [rectangle_sum_eq hfin]
    simpa only [div_mul_eq_mul_div,one_mul] using hg
  rw [←rectangle_sum_eq hfin]
  exact hh.trans hu

/-- The actual ordinate-weight API used by the new four-height spectral
program. All moment and count budgets are derived from regular source leaves. -/
theorem source_ordinate_envelope
    (h:WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH:IEANTN.RiemannHypothesisUpTo WinnerOriginalScalars.height)
    {sigma tau t:ℝ} (hs:(3/4:ℝ)≤sigma) (hs':sigma≤7/8)
    (htau:28≤tau) (htauH:WinnerDensityA.H≤exp tau) (ht:exp tau≤t) :
    (2*Real.pi/t)*IEANTN.zetaZeroesSum (Ioo sigma 1) (Ioc 0 t)
      (fun rho↦t/Real.pi*(1/rho.im)+2)≤envelope sigma tau := by
  have htH:=htauH.trans ht
  have ht0:0<t:=by norm_num [WinnerDensityA.H] at htH; linarith
  have hfin:=finite_zero_rectangle (Ioo sigma 1) (T:=t)
  have he:IEANTN.zetaZeroesSum (Ioo sigma 1) (Ioc 0 t) (fun rho↦t/Real.pi*(1/rho.im)+2)=
      t/Real.pi*IEANTN.zetaZeroesSum (Ioo sigma 1) (Ioc 0 t) (fun rho↦1/rho.im)+
      2*IEANTN.zetaZeroesSum (Ioo sigma 1) (Ioc 0 t) (fun _↦(1:ℝ)):=by
    rw [rectangle_sum_eq hfin,rectangle_sum_eq hfin,rectangle_sum_eq hfin,
      Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro rho _
    ring
  have hR:=reciprocal_moment h hRH hs hs' htH
  have hN:=profile_count_closed h hRH 0 hs hs' (by simpa only [anchor_zero] using htH)
  have hB:=WinnerDensityA.boundary_antitone (coeff_nonneg 0 sigma) (by norm_num : (0:ℝ)≤6) hs hs'
    (show 1<exp tau by rw [one_lt_exp_iff]; linarith) (by simpa using htau)
  have hBd:=hB (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht
  rw [he]
  have hh:=mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left hR (show 0≤t/Real.pi by positivity))
      (mul_le_mul_of_nonneg_left hN (show (0:ℝ)≤2 by norm_num))) (show 0≤2*Real.pi/t by positivity)
  have hp:=mul_le_mul_of_nonneg_left hBd (show 0≤4*Real.pi by positivity)
  unfold envelope
  have hid:(2*Real.pi/t)*(t/Real.pi*moment sigma+2*WinnerDensityA.poly (coeff 0 sigma) 6 sigma t)=
      2*moment sigma+4*Real.pi*(WinnerDensityA.poly (coeff 0 sigma) 6 sigma t/t):=by field_simp; ring
  rw [hid] at hh
  linarith
#print axioms reciprocal_moment
#print axioms source_ordinate_envelope
end PVEvolutionA.SlopedMoment
