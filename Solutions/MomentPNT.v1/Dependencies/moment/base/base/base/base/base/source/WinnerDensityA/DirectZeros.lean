/- Copyright (c) 2026 IEANTN contributors. Released under Apache2.0. -/
import WinnerDensityA.DirectPrimePower
import WinnerDensityA.Spectral
import ZeroSymmetry
namespace WinnerDirectKernel
open Real Set MeasureTheory IEANTN Complex
open CH2QRH
set_option maxHeartbeats 0
noncomputable def positiveZeros (T : ℝ) : Finset ℂ :=
  (CH2Section7Z.finite_zeros_Ioc (a:=0) (b:=T) le_rfl).toFinset
noncomputable def pairedZeros (T : ℝ) : Finset (ℂ×Bool) := (positiveZeros T).product {false,true}
noncomputable def pairZ (q : ℂ×Bool) : ℂ := if q.2 then q.1 else (starRingEnd ℂ) q.1
noncomputable def pairW (q : ℂ×Bool) : ℝ := (IEANTN.zetaOrder q.1:ℝ)
noncomputable def pairedPsiBudget (T L : ℝ) : ℝ :=
  ∑ q ∈ pairedZeros T,pairW q*Real.exp ((pairZ q).re*L)/|(pairZ q).im|

 theorem positive_mem {T : ℝ} {rho : ℂ} (hr : rho∈positiveZeros T) :
    rho∈IEANTN.zetaZeroesIn Set.univ (Ioc 0 T) := (Set.Finite.mem_toFinset _).mp hr

 theorem positive_re_lower (hqrh : IEANTN.ZetaZeroFreeHalfPlane (7/8))
    {T : ℝ} {rho : ℂ} (hr : rho∈positiveZeros T) : (1/8:ℝ)≤rho.re := by
  have hm:=positive_mem hr
  have href:=CH2QRH.zeroReflect_mem hm
  have hq:=CH2QRH.re_le_boundary hqrh href.2.2 href.2.1.1
  simp only [CH2QRH.zeroReflect,Complex.sub_re,Complex.one_re,Complex.conj_re] at hq
  linarith

 theorem positive_im_lower (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    {T : ℝ} {rho : ℂ} (hr : rho∈positiveZeros T) : (14:ℝ)≤rho.im := by
  have hm:=positive_mem hr
  by_contra hh
  have hlt : rho.im<14 := lt_of_not_ge hh
  have he : rho∈IEANTN.zetaZeroesIn Set.univ (Ioo 0 (14.134725/IEANTN.margin 0)) := by
    refine ⟨trivial,⟨hm.2.1.1,?_⟩,hm.2.2⟩
    norm_num [IEANTN.margin] at *
    linarith
  change IEANTN.zetaZeroesIn Set.univ (Ioo 0 (14.134725/IEANTN.margin 0))=∅ at hlow
  rw [hlow] at he
  exact he

 theorem pair_properties (hqrh : IEANTN.ZetaZeroFreeHalfPlane (7/8))
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    {T : ℝ} {q : ℂ×Bool} (hq : q∈pairedZeros T) :
    0≤pairW q ∧ (1/8:ℝ)≤(pairZ q).re ∧ (14:ℝ)≤|(pairZ q).im| := by
  have hm:=Finset.mem_product.mp hq
  have hr:=positive_mem hm.1
  have hw:=CH2Section7Z.zetaOrder_nonneg_of_mem Set.Ioc_subset_Ioi_self hr
  have hre:=positive_re_lower hqrh hm.1
  have him:=positive_im_lower hlow hm.1
  have himp:=hr.2.1.1
  rcases q with ⟨rho,b⟩
  cases b <;> simpa [pairW,pairZ,abs_of_pos himp] using And.intro hw (And.intro hre him)

 theorem paired_budget_eq (T L : ℝ) : pairedPsiBudget T L=
      2*∑ rho∈positiveZeros T,(IEANTN.zetaOrder rho:ℝ)*Real.exp (rho.re*L)/rho.im := by
  unfold pairedPsiBudget pairedZeros
  rw [Finset.product_eq_sprod,Finset.sum_product]
  have he : ∀rho∈positiveZeros T,
      (∑ b∈({false,true}:Finset Bool),pairW (rho,b)*Real.exp ((pairZ (rho,b)).re*L)/|(pairZ (rho,b)).im|)=
      2*((IEANTN.zetaOrder rho:ℝ)*Real.exp (rho.re*L)/rho.im) := by
    intro rho hr
    have hi:=(positive_mem hr).2.1.1
    simp [pairW,pairZ,abs_of_pos hi]
    ring
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro rho hr
  exact he rho hr

/-- The exact positive-zero weights needed by direct pi are no larger than the
existing actual CH2 spectral weights. -/
 theorem paired_budget_le_raw {T L : ℝ} (hT : 0<T) :
    pairedPsiBudget T L≤Real.exp L*WinnerDensityA.rawSpectral T (Real.exp L) := by
  rw [paired_budget_eq]
  have hfin:=CH2Section7Z.finite_zeros_Ioc (a:=0) (b:=T) le_rfl
  have he : Real.exp L*WinnerDensityA.rawSpectral T (Real.exp L)=
      ∑rho∈positiveZeros T,(2/rho.im+4*Real.pi/T)*(IEANTN.zetaOrder rho:ℝ)*Real.exp (rho.re*L) := by
    unfold WinnerDensityA.rawSpectral
    rw [CH2Section7Z.zetaZeroesSum_eq_sum hfin]
    change Real.exp L*((2*Real.pi/T)*∑rho∈positiveZeros T,
      ((T/Real.pi*(1/rho.im)+2)*Real.exp L^(rho.re-1))*(IEANTN.zetaOrder rho:ℝ))=_
    rw [Finset.mul_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro rho hr
    have hi:=(positive_mem hr).2.1.1
    rw [Real.rpow_def_of_pos (Real.exp_pos L),Real.log_exp]
    have hExp : Real.exp L*Real.exp (L*(rho.re-1))=Real.exp (rho.re*L) := by
      rw [←Real.exp_add]
      congr 1
      ring
    have hleft : Real.exp L*((2*Real.pi/T)*
      (((T/Real.pi*(1/rho.im)+2)*Real.exp (L*(rho.re-1)))*(IEANTN.zetaOrder rho:ℝ)))=
      ((2*Real.pi/T)*(T/Real.pi*(1/rho.im)+2)*(IEANTN.zetaOrder rho:ℝ))*
        (Real.exp L*Real.exp (L*(rho.re-1))) := by ring
    rw [hleft,hExp]
    field_simp [hT.ne',Real.pi_ne_zero,hi.ne']
    <;> ring
  rw [he,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro rho hr
  have hm:=positive_mem hr
  have hi:=hm.2.1.1
  have hw:=CH2Section7Z.zetaOrder_nonneg_of_mem Set.Ioc_subset_Ioi_self hm
  have hp : 0≤4*Real.pi/T*(IEANTN.zetaOrder rho:ℝ)*Real.exp (rho.re*L) := by positivity
  calc
    2*((zetaOrder rho:ℝ)*Real.exp (rho.re*L)/rho.im)≤
      2*((zetaOrder rho:ℝ)*Real.exp (rho.re*L)/rho.im)+4*Real.pi/T*(zetaOrder rho:ℝ)*Real.exp (rho.re*L) := by linarith
    _ = _ := by ring

 theorem paired_kernel_bound (hqrh : IEANTN.ZetaZeroFreeHalfPlane (7/8))
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    {T v L : ℝ} (hT : 0<T) (hv : 0<v) (hL : v≤L) :
    ‖∑ q∈pairedZeros T,(pairW q:ℂ)*piKernel (pairZ q) v L‖≤
      highFactor (1/8) 14 v L*(Real.exp L*WinnerDensityA.rawSpectral T (Real.exp L))/L := by
  have hh:=high_sum_bound (pairedZeros T) pairZ pairW (by norm_num : (0:ℝ)<1/8)
    (by norm_num : (0:ℝ)<14) hv hL
    (fun q hq=>(pair_properties hqrh hlow hq).1)
    (fun q hq=>(pair_properties hqrh hlow hq).2.1)
    (fun q hq=>(pair_properties hqrh hlow hq).2.2)
  apply hh.trans
  apply div_le_div_of_nonneg_right _ (hv.trans_le hL).le
  apply mul_le_mul_of_nonneg_left (paired_budget_le_raw hT)
  have hLp : 0<L := hv.trans_le hL
  unfold highFactor
  positivity

#print axioms paired_budget_le_raw
#print axioms paired_kernel_bound
end WinnerDirectKernel
