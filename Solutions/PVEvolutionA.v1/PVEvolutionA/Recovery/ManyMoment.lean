/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import PVEvolutionA.Recovery.ManyMomentModel
import PVEvolutionA.SlopedMoment
namespace PVEvolutionA.Recovery.Model
open Real Set MeasureTheory Filter Topology CH2QRH WinnerDensityA.Piecewise
set_option maxHeartbeats 0

theorem step_count_closed
    (accepted : ∀j:Fin 18,WinnerProgramA.acceptUpper (GaussianBasis.output j) [(GaussianBasis.spec j).cap]=true)
    (h : WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH : IEANTN.RiemannHypothesisUpTo WinnerOriginalScalars.height)
    {sigma T:ℝ} (hs:(3/4:ℝ)≤sigma) (hs':sigma≤7/8) (hT:WinnerDensityA.H≤T) :
    IEANTN.zetaZeroesSum (Ioo sigma 1) (Ioc 0 T) (fun _↦(1:ℝ))≤step sigma T := by
  obtain ⟨j,hj,hja,hjc⟩ := ManyStep.exists_selected (c:=Profiles.coeff sigma) (n:=127)
    Profiles.anchor_mono (by simpa only [Profiles.anchor_zero] using hT)
  have hp := Profiles.count_closed accepted h hRH j hs hs' hja
  unfold step ManyStep.majorant
  rw [hjc]
  simpa only [WinnerDensityA.poly,p,q] using hp

theorem reciprocal_moment
    (accepted : ∀j:Fin 18,WinnerProgramA.acceptUpper (GaussianBasis.output j) [(GaussianBasis.spec j).cap]=true)
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
  have hi : IntegrableOn (fun u=>step sigma u/u^2) (Ioi WinnerDensityA.H) := by
    exact ManyStep.integrable (a:=Profiles.anchor) (c:=Profiles.coeff sigma) (n:=127) (d:=6)
      hA hl hp hp' hq'
  have hb : Tendsto (fun u=>step sigma u/u) atTop (𝓝 0) := by
    exact ManyStep.boundary_zero (c:=Profiles.coeff sigma) (n:=127) (d:=6)
      Profiles.anchor_mono hp'
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
    exact PVEvolutionA.SlopedMoment.partial_closed_le.trans (step_count_closed accepted h hRH hs hs' hu)
  have hg:=finite_reciprocal_global S Complex.im (fun rho↦(IEANTN.zetaOrder rho:ℝ))
    (by linarith) hT hgamma (step sigma) hi hb hc
  have hu : (∫u in Ioi WinnerDensityA.H,step sigma u/u^2)≤moment sigma := by
    exact ManyStep.integral_upper (a:=Profiles.anchor) (c:=Profiles.coeff sigma) (n:=127) (d:=6)
      hA hl hp hp' hq hq' (fun j hj=>Profiles.height_lt_anchor hj)
      (Profiles.coeff_nonneg sigma 0)
      (fun j _=>Profiles.coeff_antitone hs' (Nat.le_succ j))
  rw [rectangle_sum_eq hfin]
  have hh:IEANTN.zetaZeroesSum (Ioo sigma 1) (Ioc 0 T) (fun rho↦1/rho.im)≤
      ∫u in Ioi WinnerDensityA.H,step sigma u/u^2 := by
    rw [rectangle_sum_eq hfin]
    simpa only [div_mul_eq_mul_div,one_mul] using hg
  rw [←rectangle_sum_eq hfin]
  exact hh.trans hu

theorem source_ordinate_envelope
    (accepted : ∀j:Fin 18,WinnerProgramA.acceptUpper (GaussianBasis.output j) [(GaussianBasis.spec j).cap]=true)
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
  have hR:=reciprocal_moment accepted h hRH hs hs' htH
  have hN:=Profiles.count_closed accepted h hRH 0 hs hs' (by simpa only [Profiles.anchor_zero] using htH)
  have hB:=WinnerDensityA.boundary_antitone (Profiles.coeff_nonneg sigma 0) (by norm_num : (0:ℝ)≤6) hs hs'
    (show 1<exp tau by rw [one_lt_exp_iff]; linarith) (by simpa using htau)
  have hBd:=hB (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht
  rw [he]
  have hh:=mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left hR (show 0≤t/Real.pi by positivity))
      (mul_le_mul_of_nonneg_left hN (show (0:ℝ)≤2 by norm_num))) (show 0≤2*Real.pi/t by positivity)
  have hp:=mul_le_mul_of_nonneg_left hBd (show 0≤4*Real.pi by positivity)
  unfold envelope
  have hid:(2*Real.pi/t)*(t/Real.pi*moment sigma+2*WinnerDensityA.poly (Profiles.coeff sigma 0) 6 sigma t)=
      2*moment sigma+4*Real.pi*(WinnerDensityA.poly (Profiles.coeff sigma 0) 6 sigma t/t):=by field_simp; ring
  rw [hid] at hh
  linarith

#print axioms reciprocal_moment
#print axioms source_ordinate_envelope
end PVEvolutionA.Recovery.Model
