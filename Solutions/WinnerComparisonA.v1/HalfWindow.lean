/- Copyright (c)2026 IEANTN contributors. Released under Apache2.0. -/
import ZeroSymmetry
import DensityTail
import Mathlib.Tactic
namespace WinnerHalfWindow
open Real Set CH2QRH
set_option maxHeartbeats 0

/-- Exact finite multiplicity decomposition of the total closed count. -/
theorem total_closed_difference {H T:ℝ} (hH:0≤H) (hHT:H≤T) :
    IEANTN.zetaZeroesSum Set.univ (Ioc H T) (fun _↦(1:ℝ))=
      ZeroCount.v1.zetaNClosed T-ZeroCount.v1.zetaNClosed H := by
  classical
  have hall:=CH2Section7Z.finite_zeros_Ioc (a:=0) (b:=T) le_rfl
  have hlow:=CH2Section7Z.finite_zeros_Ioc (a:=0) (b:=H) le_rfl
  have hhigh:=CH2Section7Z.finite_zeros_Ioc (a:=H) (b:=T) hH
  have hd:Disjoint hlow.toFinset hhigh.toFinset:=by
    apply Finset.disjoint_left.mpr
    intro rho hl hh
    have hl':=(Set.Finite.mem_toFinset hlow).mp hl
    have hh':=(Set.Finite.mem_toFinset hhigh).mp hh
    linarith [hl'.2.1.2,hh'.2.1.1]
  have he:hall.toFinset=hlow.toFinset∪hhigh.toFinset:=by
    ext rho
    simp only [Finset.mem_union,Set.Finite.mem_toFinset]
    constructor
    · intro hr
      by_cases hcut:rho.im≤H
      · exact Or.inl ⟨trivial,⟨hr.2.1.1,hcut⟩,hr.2.2⟩
      · exact Or.inr ⟨trivial,⟨lt_of_not_ge hcut,hr.2.1.2⟩,hr.2.2⟩
    · rintro (hr|hr)
      · exact ⟨trivial,⟨hr.2.1.1,hr.2.1.2.trans hHT⟩,hr.2.2⟩
      · exact ⟨trivial,⟨hH.trans_lt hr.2.1.1,hr.2.1.2⟩,hr.2.2⟩
  change IEANTN.zetaZeroesSum Set.univ (Ioc H T) (fun _↦(1:ℝ))=
    IEANTN.zetaZeroesSum Set.univ (Ioc 0 T) (fun _↦(1:ℝ))-
    IEANTN.zetaZeroesSum Set.univ (Ioc 0 H) (fun _↦(1:ℝ))
  rw [rectangle_sum_eq hhigh,rectangle_sum_eq hall,rectangle_sum_eq hlow,he,Finset.sum_union hd]
  simp only [one_mul]
  ring

/-- Each high-real-part zero has a distinct reflected partner at the same
ordinate and with the same actual multiplicity. Verified RH removes every
such pair at ordinates at most H. No new zero-count oracle is assumed. -/
theorem twice_high_closed_le_total_difference {sigma H T:ℝ}
    (hs:(1/2:ℝ)≤sigma) (hH:0≤H) (hHT:H≤T)
    (hRH:IEANTN.RiemannHypothesisUpTo H) :
    2*IEANTN.zetaZeroesSum (Ioo sigma 1) (Ioc 0 T) (fun _↦(1:ℝ))≤
      ZeroCount.v1.zetaNClosed T-ZeroCount.v1.zetaNClosed H := by
  classical
  have hfin:=finite_zero_rectangle (Ioo sigma 1) (T:=T)
  have hall:=CH2Section7Z.finite_zeros_Ioc (a:=H) (b:=T) hH
  let S:=hfin.toFinset
  let R:=S.image zeroReflect
  have hlow:∀rho∈S,H<rho.im:=by
    intro rho hr
    have hz:=(Set.Finite.mem_toFinset hfin).mp hr
    by_contra hn
    have hbad:rho∈IEANTN.zetaZeroesIn (Ioo (1/2) 1) (Icc 0 H):=
      ⟨⟨hs.trans_lt hz.1.1,hz.1.2⟩,⟨hz.2.1.1.le,not_lt.mp hn⟩,hz.2.2⟩
    exact hRH.false ⟨rho,hbad⟩
  have hS:∀rho∈S,rho∈hall.toFinset:=by
    intro rho hr
    have hz:=(Set.Finite.mem_toFinset hfin).mp hr
    exact (Set.Finite.mem_toFinset hall).mpr ⟨trivial,⟨hlow rho hr,hz.2.1.2⟩,hz.2.2⟩
  have hR:∀rho∈R,rho∈hall.toFinset:=by
    intro rho hr
    obtain ⟨z,hz,he⟩:=Finset.mem_image.mp hr
    have hz':=(Set.Finite.mem_toFinset hfin).mp hz
    have hallz:z∈IEANTN.zetaZeroesIn Set.univ (Ioc 0 T):=⟨trivial,hz'.2.1,hz'.2.2⟩
    have href:=zeroReflect_mem hallz
    rw [←he]
    apply (Set.Finite.mem_toFinset hall).mpr
    refine ⟨trivial,⟨?_,?_⟩,href.2.2⟩
    · simpa only [zeroReflect,Complex.sub_im,Complex.one_im,Complex.conj_im,zero_sub,neg_neg] using hlow z hz
    · simpa only [zeroReflect,Complex.sub_im,Complex.one_im,Complex.conj_im,zero_sub,neg_neg] using hz'.2.1.2
  have hd:Disjoint S R:=by
    apply Finset.disjoint_left.mpr
    intro rho hr hrr
    obtain ⟨z,hz,he⟩:=Finset.mem_image.mp hrr
    have hre: sigma<rho.re:=((Set.Finite.mem_toFinset hfin).mp hr).1.1
    have hze: sigma<z.re:=((Set.Finite.mem_toFinset hfin).mp hz).1.1
    have hh:rho.re=1-z.re:=by rw [←he];simp only [zeroReflect,Complex.sub_re,Complex.one_re,Complex.conj_re]
    linarith
  have hsumR:(∑rho∈R,(IEANTN.zetaOrder rho:ℝ))=∑rho∈S,(IEANTN.zetaOrder rho:ℝ):=by
    rw [show R=S.image zeroReflect from rfl,Finset.sum_image zeroReflect_involutive.injective.injOn]
    apply Finset.sum_congr rfl
    intro rho hr
    rw [zetaOrder_zeroReflect (((Set.Finite.mem_toFinset hfin).mp hr).2.1.1.ne')]
  have hu:S∪R⊆hall.toFinset:=by
    intro rho hr
    rcases Finset.mem_union.mp hr with hr|hr
    · exact hS rho hr
    · exact hR rho hr
  have hsum:(∑rho∈S∪R,(IEANTN.zetaOrder rho:ℝ))≤∑rho∈hall.toFinset,(IEANTN.zetaOrder rho:ℝ):=by
    apply Finset.sum_le_sum_of_subset_of_nonneg hu
    intro rho hr _
    have hz:=(Set.Finite.mem_toFinset hall).mp hr
    exact CH2Section7Z.zetaOrder_nonneg_of_mem (J:=Ioc 0 T) Ioc_subset_Ioi_self
      ⟨trivial,⟨hH.trans_lt hz.2.1.1,hz.2.1.2⟩,hz.2.2⟩
  rw [Finset.sum_union hd,hsumR] at hsum
  rw [←total_closed_difference hH hHT,rectangle_sum_eq hall,rectangle_sum_eq hfin]
  simp only [one_mul]
  change 2*(∑rho∈S,(IEANTN.zetaOrder rho:ℝ))≤_
  linarith

/-- The actual closed off-critical count has the half-window normalization. -/
theorem high_closed_le_half_difference {sigma H T:ℝ}
    (hs:(1/2:ℝ)≤sigma) (hH:0≤H) (hHT:H≤T)
    (hRH:IEANTN.RiemannHypothesisUpTo H) :
    IEANTN.zetaZeroesSum (Ioo sigma 1) (Ioc 0 T) (fun _↦(1:ℝ))≤
      (ZeroCount.v1.zetaNClosed T-ZeroCount.v1.zetaNClosed H)/2 := by
  linarith [twice_high_closed_le_total_difference hs hH hHT hRH]

/-- Physical T normalization used by the source density/window program. -/
theorem high_closed_div_height {sigma H T:ℝ}
    (hs:(1/2:ℝ)≤sigma) (hH:0≤H) (hHT:H≤T) (hT:0<T)
    (hRH:IEANTN.RiemannHypothesisUpTo H) :
    IEANTN.zetaZeroesSum (Ioo sigma 1) (Ioc 0 T) (fun _↦(1:ℝ))/T≤
      (ZeroCount.v1.zetaNClosed T-ZeroCount.v1.zetaNClosed H)/(2*T) := by
  have hh:=div_le_div_of_nonneg_right (high_closed_le_half_difference hs hH hHT hRH) hT.le
  simpa only [div_div] using hh
#print axioms twice_high_closed_le_total_difference
#print axioms high_closed_div_height
end WinnerHalfWindow
