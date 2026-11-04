/- Copyright (c) 2026 IEANTN contributors. Released under Apache2.0. -/
import WinnerDensityA.DirectCHJPairing
import OriginalScalarSemantics
namespace WinnerDirectKernel
open Real Set MeasureTheory IEANTN
set_option maxHeartbeats 0

noncomputable def highPairedZeros (T : ℝ) : Finset (ℂ×Bool) :=
  (pairedZeros T).filter (fun q => WinnerOriginalScalars.height < |(pairZ q).im|)
noncomputable def lowPairedZeros (T : ℝ) : Finset (ℂ×Bool) :=
  (pairedZeros T).filter (fun q => |(pairZ q).im| ≤ WinnerOriginalScalars.height)

/-- At the already supplied verified-RH height, the high-ordinate integrated
kernel overhead is below one part in a billion, without a new finite check. -/
theorem rh_high_factor {L : ℝ} (hL : 300 ≤ L) :
    highFactor (1/8) WinnerOriginalScalars.height ((3/4)*L) L ≤
      1+1/1000000000 := by
  have hLp : 0 < L := by linarith
  have hvp : 0 < (3/4:ℝ)*L := by positivity
  have hH : 0 < WinnerOriginalScalars.height := by norm_num [WinnerOriginalScalars.height]
  have he : exp (-(1/8:ℝ)*(L-(3/4)*L)) ≤ 1 := exp_le_one_iff.mpr (by linarith)
  have h1 : 1/(WinnerOriginalScalars.height*L) ≤ 1/(WinnerOriginalScalars.height*300) := by gcongr
  have hfrac2 : L/(WinnerOriginalScalars.height*((3/4)*L)^2)=
      16/(9*WinnerOriginalScalars.height*L) := by field_simp;ring
  have hfrac3 : 2*L/(WinnerOriginalScalars.height*(1/8)*((3/4)*L)^3)=
      1024/(27*WinnerOriginalScalars.height*L^2) := by field_simp;ring
  have h2 : exp (-(1/8:ℝ)*(L-(3/4)*L))*L/(WinnerOriginalScalars.height*((3/4)*L)^2) ≤
      16/(9*WinnerOriginalScalars.height*300) := by
    calc _ ≤ L/(WinnerOriginalScalars.height*((3/4)*L)^2) := by
           apply div_le_div_of_nonneg_right _ (by positivity)
           simpa using mul_le_mul_of_nonneg_right he hLp.le
         _ = _ := hfrac2
         _ ≤ _ := by gcongr
  have h3 : 2*L/(WinnerOriginalScalars.height*(1/8)*((3/4)*L)^3) ≤
      1024/(27*WinnerOriginalScalars.height*(300:ℝ)^2) := by
    rw [hfrac3]
    gcongr
  unfold highFactor
  norm_num [WinnerOriginalScalars.height] at h1 h2 h3 ⊢
  linarith

 theorem high_paired_budget_le_raw {T L : ℝ} (hT : 0 < T) :
    (∑q∈highPairedZeros T,pairW q*exp ((pairZ q).re*L)/|(pairZ q).im|) ≤
      exp L*WinnerDensityA.rawSpectral T (exp L) := by
  apply le_trans _ (paired_budget_le_raw (L:=L) hT)
  unfold pairedPsiBudget highPairedZeros
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
  intro q hq _
  have hw : 0 ≤ pairW q := by
    unfold pairW
    exact CH2Section7Z.zetaOrder_nonneg_of_mem Ioc_subset_Ioi_self
      (positive_mem (Finset.mem_product.mp hq).1)
  positivity

 theorem high_paired_kernel_bound
    (hqrh : ZetaZeroFreeHalfPlane (7/8))
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    {T v L : ℝ} (hT : 0 < T) (hv : 0 < v) (hL : v ≤ L) :
    ‖∑q∈highPairedZeros T,(pairW q:ℂ)*piKernel (pairZ q) v L‖ ≤
      highFactor (1/8) WinnerOriginalScalars.height v L*
        (exp L*WinnerDensityA.rawSpectral T (exp L))/L := by
  have hH : 0 < WinnerOriginalScalars.height := by norm_num [WinnerOriginalScalars.height]
  have hh:=high_sum_bound (highPairedZeros T) pairZ pairW (by norm_num : (0:ℝ)<1/8)
    hH hv hL
    (fun q hq=>(pair_properties hqrh hlow (Finset.mem_filter.mp hq).1).1)
    (fun q hq=>(pair_properties hqrh hlow (Finset.mem_filter.mp hq).1).2.1)
    (fun q hq=>(Finset.mem_filter.mp hq).2.le)
  apply hh.trans
  apply div_le_div_of_nonneg_right _ (hv.trans_le hL).le
  apply mul_le_mul_of_nonneg_left (high_paired_budget_le_raw hT)
  have hLp : 0 < L := hv.trans_le hL
  unfold highFactor
  positivity

 theorem split_paired_kernel (T v L : ℝ) :
    (∑q∈pairedZeros T,(pairW q:ℂ)*piKernel (pairZ q) v L)=
      (∑q∈lowPairedZeros T,(pairW q:ℂ)*piKernel (pairZ q) v L)+
      (∑q∈highPairedZeros T,(pairW q:ℂ)*piKernel (pairZ q) v L) := by
  classical
  unfold lowPairedZeros highPairedZeros
  simpa only [not_le] using (Finset.sum_filter_add_sum_filter_not
    (pairedZeros T) (fun q => |(pairZ q).im| ≤ WinnerOriginalScalars.height)
    (fun q => (pairW q:ℂ)*piKernel (pairZ q) v L)).symm

#print axioms rh_high_factor
#print axioms high_paired_kernel_bound
#print axioms split_paired_kernel
end WinnerDirectKernel
