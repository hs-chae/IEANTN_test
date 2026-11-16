import SynergyAnalytic.ReciprocalBoundary
import SynergyAnalytic.TailFour
import SynergyAnalytic.LogBoundary
import WinnerDensityA.GlobalReciprocal
namespace SynergyAnalytic
open Real Set MeasureTheory Filter Topology CH2QRH
set_option maxHeartbeats 0
theorem partial_closed_le {sigma T u:ℝ} :
    (∑rho∈(finite_zero_rectangle (Ioo sigma 1) (T:=T)).toFinset,
      if rho.im ≤  u then (IEANTN.zetaOrder rho:ℝ) else 0) ≤ 
    IEANTN.zetaZeroesSum (Ioo sigma 1) (Ioc 0 u) (fun _↦(1:ℝ)) := by
  classical
  let S:=(finite_zero_rectangle (Ioo sigma 1) (T:=T)).toFinset
  have hu:=finite_zero_rectangle (Ioo sigma 1) (T:=u)
  rw [rectangle_sum_eq hu]
  simp only [one_mul]
  change (∑rho∈S,if rho.im ≤  u then (IEANTN.zetaOrder rho:ℝ) else 0) ≤  _
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


/-- Actual zeta reciprocal sum from finite whole-height cells, plus the proved
analytic far tail. Its count premises are discharged by height_cell_actual_count
and coarse_count_closed; no reciprocal/moment conclusion is assumed. -/
theorem actual_reciprocal_from_count_caps {a caps : ℕ→ℝ} {n : ℕ} {sigma T K : ℝ}
    (ha : Monotone a) (ha0 : a 0=WinnerOriginalScalars.height) (han : a n=Real.exp 60)
    (hK : 0 ≤ K) (hRH : IEANTN.RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hs : (3/4:ℝ) ≤ sigma) (hs' : sigma ≤ 7/8) (hT : WinnerOriginalScalars.height ≤ T)
    (hcaps : ∀i<n,∀u∈Icc (a i) (a (i+1)),
      IEANTN.zetaZeroesSum (Ioo sigma 1) (Ioc 0 u) (fun _=>(1:ℝ)) ≤ caps i+6*Real.log u^2)
    (hcoarse : ∀u,Real.exp 60 ≤ u→
      IEANTN.zetaZeroesSum (Ioo sigma 1) (Ioc 0 u) (fun _=>(1:ℝ)) ≤ 
        K*u^(8*(1-sigma)/3)*Real.log u^(5-2*sigma)+6*Real.log u^2) :
    IEANTN.zetaZeroesSum (Ioo sigma 1) (Ioc 0 T) (fun rho=>1/rho.im) ≤ 
      (∑i∈Finset.range n,caps i*(1/a i-1/a (i+1)))+
      (K/1000000000)*Real.exp (160*((7/8)-sigma))+1/100000000 := by
  classical
  have hfin := finite_zero_rectangle (Ioo sigma 1) (T:=T)
  let S := hfin.toFinset
  have hA : 0<a 0 := by rw [ha0];norm_num [WinnerOriginalScalars.height]
  have hgamma : ∀rho∈S,a 0<rho.im ∧rho.im ≤ T := by
    intro rho hrho
    have hz := (Set.Finite.mem_toFinset hfin).mp hrho
    refine ⟨?_,hz.2.1.2⟩
    rw [ha0]
    by_contra he
    have hzlow : rho∈IEANTN.zetaZeroesIn (Ioo (1/2) 1) (Icc 0 WinnerOriginalScalars.height) :=
      ⟨⟨by linarith [hz.1.1],hz.1.2⟩,⟨hz.2.1.1.le,not_lt.mp he⟩,hz.2.2⟩
    exact hRH.false ⟨rho,hzlow⟩
  have hg : ContinuousOn (fun u:ℝ=>K*u^(8*(1-sigma)/3)*Real.log u^(5-2*sigma)) (Ici (a n)) := by
    rw [han]
    intro u hu
    have hu1 : 1<u := (Real.one_lt_exp_iff.mpr (by norm_num : (0:ℝ)<60)).trans_le hu
    have hu0 : u≠0 := (lt_trans zero_lt_one hu1).ne'
    have hlu : Real.log u≠0 := (Real.log_pos hu1).ne'
    have hpow := Real.continuousAt_rpow_const u (8*(1-sigma)/3) (Or.inl hu0)
    have hlog := (Real.continuousAt_log hu0).rpow_const (p:=5-2*sigma) (Or.inl hlu)
    exact ((hpow.const_mul K).mul hlog).continuousWithinAt
  have hh : (∑rho∈S,(IEANTN.zetaOrder rho:ℝ)/rho.im) ≤
      (∑i∈Finset.range n,caps i*(1/a i-1/a (i+1)))+
        (K/1000000000)*Real.exp (160*((7/8)-sigma))+1/100000000 :=
    finite_reciprocal_cells_tail_boundary S Complex.im (fun rho=>(IEANTN.zetaOrder rho:ℝ))
    ha hA hgamma
    (fun i hin u hu=>(partial_closed_le (sigma:=sigma) (T:=T) (u:=u)).trans (hcaps i hin u hu))
    hg (fun u hu=>(partial_closed_le (sigma:=sigma) (T:=T) (u:=u)).trans
      (hcoarse u (by simpa only [han] using hu)))
    (fun B hB=>by
      rw [han]
      exact tail_integral_four_affine hs hs' (by simpa only [han] using hB) hK)
    (by
      intro u hu
      have hu0 : u≠0 := (hA.trans_le hu).ne'
      exact (((Real.continuousAt_log hu0).pow 2).const_mul 6).continuousWithinAt)
    (fun B hB=>by simpa only [ha0] using log_boundary_budget (by simpa only [ha0] using hB))
  rw [rectangle_sum_eq hfin]
  convert hh using 1
  apply Finset.sum_congr rfl
  intro rho hrho
  ring

#print axioms actual_reciprocal_from_count_caps
end SynergyAnalytic
