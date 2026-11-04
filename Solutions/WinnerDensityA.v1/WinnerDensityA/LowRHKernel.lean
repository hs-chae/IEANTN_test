/- Copyright (c) 2026 IEANTN contributors. Released under Apache2.0. -/
import WinnerDensityA.DirectRHHigh
import WinnerDensityA.DirectRayParameters
import ZeroCount
namespace WinnerDirectKernel
open Real Set MeasureTheory IEANTN CH2QRH
set_option maxHeartbeats 0

/-- The original finite RH input, together with reflection, puts every low
positive zero used by the actual paired sum on the critical line. -/
theorem positive_low_re_half
    (hqrh : ZetaZeroFreeHalfPlane (7/8))
    (hRH : RiemannHypothesisUpTo WinnerOriginalScalars.height)
    {T : ℝ} {rho : ℂ} (hr : rho∈positiveZeros T)
    (hlo : rho.im≤WinnerOriginalScalars.height) : rho.re=(1/2:ℝ) := by
  have hz:=positive_mem hr
  have hu:=re_le_boundary hqrh hz.2.2 hz.2.1.1
  have hl:=positive_re_lower hqrh hr
  have hle : rho.re≤(1/2:ℝ) := by
    by_contra hn
    exact hRH.false ⟨rho,⟨⟨lt_of_not_ge hn,by linarith⟩,
      ⟨hz.2.1.1.le,hlo⟩,hz.2.2⟩⟩
  have hge : (1/2:ℝ)≤rho.re := by
    by_contra hn
    have href:=zeroReflect_mem hz
    have hre : (1/2:ℝ)<(zeroReflect rho).re ∧ (zeroReflect rho).re<1 := by
      simp only [zeroReflect,Complex.sub_re,Complex.one_re,Complex.conj_re]
      constructor <;> linarith [lt_of_not_ge hn]
    have hi : (zeroReflect rho).im=rho.im := by simp [zeroReflect]
    exact hRH.false ⟨zeroReflect rho,⟨hre,⟨by rw [hi];exact hz.2.1.1.le,
      by rw [hi];exact hlo⟩,href.2.2⟩⟩
  exact le_antisymm hle hge

 theorem low_pair_re_half
    (hqrh : ZetaZeroFreeHalfPlane (7/8))
    (hRH : RiemannHypothesisUpTo WinnerOriginalScalars.height)
    {T : ℝ} {q : ℂ×Bool} (hq : q∈lowPairedZeros T) : (pairZ q).re=(1/2:ℝ) := by
  have hm:=Finset.mem_filter.mp hq
  have hp:=Finset.mem_product.mp hm.1
  have hi:=(positive_mem hp.1).2.1.1
  have hlo : q.1.im≤WinnerOriginalScalars.height := by
    rcases q with ⟨rho,b⟩
    cases b <;> simpa [pairZ,abs_of_pos hi] using hm.2
  have he:=positive_low_re_half hqrh hRH hp.1 hlo
  rcases q with ⟨rho,b⟩
  cases b <;> simpa [pairZ] using he

 theorem constant_paired_budget (T L : ℝ) :
    (∑q∈pairedZeros T,pairW q*exp ((1/2:ℝ)*L)/|(pairZ q).im|)=
      2*exp (L/2)*IEANTN.zetaZeroesSum univ (Ioc 0 T) (fun rho↦1/rho.im) := by
  classical
  have hfin:=CH2Section7Z.finite_zeros_Ioc (a:=0) (b:=T) le_rfl
  rw [CH2Section7Z.zetaZeroesSum_eq_sum hfin]
  change (∑q∈pairedZeros T,pairW q*exp ((1/2:ℝ)*L)/|(pairZ q).im|)=
    2*exp (L/2)*∑rho∈positiveZeros T,(1/rho.im)*(IEANTN.zetaOrder rho:ℝ)
  unfold pairedZeros
  rw [Finset.product_eq_sprod,Finset.sum_product,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro rho hr
  have hi:=(positive_mem hr).2.1.1
  simp [pairW,pairZ,abs_of_pos hi,show (1/2:ℝ)*L=L/2 by ring]
  ring

 theorem low_paired_budget_bound
    (hqrh : ZetaZeroFreeHalfPlane (7/8))
    (hRH : RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hrvm : ZeroCount.v1.rvm_error_bound) (hsmall : ZeroCount.v1.rvm_error_small)
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    {T L : ℝ} (hT : 14≤T) :
    (∑q∈lowPairedZeros T,pairW q*exp ((pairZ q).re*L)/|(pairZ q).im|)≤
      2*exp (L/2)*(log T^2/(4*Real.pi)+log T/(2*Real.pi)) := by
  classical
  have he : (∑q∈lowPairedZeros T,pairW q*exp ((pairZ q).re*L)/|(pairZ q).im|)=
      ∑q∈lowPairedZeros T,pairW q*exp ((1/2:ℝ)*L)/|(pairZ q).im| := by
    apply Finset.sum_congr rfl
    intro q hq
    rw [low_pair_re_half hqrh hRH hq]
  rw [he]
  calc
    _ ≤ ∑q∈pairedZeros T,pairW q*exp ((1/2:ℝ)*L)/|(pairZ q).im| := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro q hq _
      have hw:=(pair_properties hqrh hlow hq).1
      positivity
    _ = 2*exp (L/2)*IEANTN.zetaZeroesSum univ (Ioc 0 T) (fun rho↦1/rho.im) := constant_paired_budget T L
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_inv_ordinates_le hrvm hsmall hlow hT) (by positivity)

/-- The low-ordinate integrated pi kernel is negligible after normalization.
This consumes finite RH already present in the winner source package. -/
theorem low_paired_kernel_tiny
    (hqrh : ZetaZeroFreeHalfPlane (7/8))
    (hRH : RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hrvm : ZeroCount.v1.rvm_error_bound) (hsmall : ZeroCount.v1.rvm_error_small)
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    {L : ℝ} (hL : 300≤L) :
    ‖∑q∈lowPairedZeros (exp (L/3)),(pairW q:ℂ)*piKernel (pairZ q) ((3/4)*L) L‖*
      (L/exp L)*exp (L/8) ≤ 1/1000000000000 := by
  have hLp : 0<L := by linarith
  have hT : 14≤exp (L/3) := by linarith [add_one_le_exp (L/3)]
  have hB:=low_paired_budget_bound hqrh hRH hrvm hsmall hlow (L:=L) hT
  rw [log_exp] at hB
  have hpol : (L/3)^2/(4*Real.pi)+(L/3)/(2*Real.pi)≤L^2+L := by
    have h1 : (L/3)^2/(4*Real.pi)≤(L/3)^2 := div_le_self (by positivity) (by linarith [Real.pi_gt_three])
    have h2 : (L/3)/(2*Real.pi)≤L/3 := div_le_self (by positivity) (by linarith [Real.pi_gt_three])
    nlinarith
  have hB' := hB.trans (mul_le_mul_of_nonneg_left hpol (by positivity : 0≤2*exp (L/2)))
  have hk:=high_sum_bound (lowPairedZeros (exp (L/3))) pairZ pairW
    (by norm_num : (0:ℝ)<1/8) (by norm_num : (0:ℝ)<14)
    (by positivity : 0<(3/4:ℝ)*L) (by linarith : (3/4:ℝ)*L≤L)
    (fun q hq=>(pair_properties hqrh hlow (Finset.mem_filter.mp hq).1).1)
    (fun q hq=>(pair_properties hqrh hlow (Finset.mem_filter.mp hq).1).2.1)
    (fun q hq=>(pair_properties hqrh hlow (Finset.mem_filter.mp hq).1).2.2)
  have hKpos : 0≤highFactor (1/8) 14 ((3/4)*L) L := by unfold highFactor;positivity
  have hfull : ‖∑q∈lowPairedZeros (exp (L/3)),(pairW q:ℂ)*piKernel (pairZ q) ((3/4)*L) L‖≤
      (1001/1000:ℝ)*(2*exp (L/2)*(L^2+L))/L := by
    apply hk.trans
    apply div_le_div_of_nonneg_right _ hLp.le
    exact mul_le_mul (direct_factor_bound hL) hB' (Finset.sum_nonneg (fun q hq↦by
      have hw:=(pair_properties hqrh hlow (Finset.mem_filter.mp hq).1).1
      positivity)) (by norm_num)
  have he : exp (L/2)/exp L*exp (L/8)=exp (-(3/8:ℝ)*L) := by
    rw [←exp_sub,←exp_add]
    congr 1
    ring
  have hnorm : ‖∑q∈lowPairedZeros (exp (L/3)),(pairW q:ℂ)*piKernel (pairZ q) ((3/4)*L) L‖*
      (L/exp L)*exp (L/8)≤(1001/500:ℝ)*(L^2+L)*exp (-(3/8:ℝ)*L) := by
    apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hfull (by positivity : 0≤L/exp L)) (exp_pos _).le).trans_eq
    calc
      _ = (1001/500:ℝ)*(L^2+L)*(exp (L/2)/exp L*exp (L/8)) := by field_simp;ring
      _ = _ := by rw [he]
  have hquad:=DudekPlattNumerics.v4.Numerics.poly_exp_decreasing 2
    (L0:=(300:ℝ)) (c:=1/4) (by norm_num) (by norm_num) hL
  have he75:=DudekPlattNumerics.v4.Numerics.exp_neg_nat_le 75
  have hsq : (L^2+L)*exp (-(3/8:ℝ)*L)≤180000/(2:ℝ)^75 := by
    have hx : L^2+L≤2*L^2 := by nlinarith
    have hexp : exp (-(3/8:ℝ)*L)≤exp (-(1/4:ℝ)*L) := exp_le_exp.mpr (by linarith)
    have hp:=mul_le_mul hx hexp (exp_pos _).le (by positivity : 0≤2*L^2)
    have he75' : exp (-(1/4:ℝ)*300)≤1/(2:ℝ)^75 := by convert he75 using 1 <;> norm_num
    have hm:=mul_le_mul_of_nonneg_left he75' (by norm_num : (0:ℝ)≤(300:ℝ)^2)
    nlinarith
  apply hnorm.trans
  calc
    _ = (1001/500:ℝ)*((L^2+L)*exp (-(3/8:ℝ)*L)) := by ring
    _ ≤ (1001/500:ℝ)*(180000/(2:ℝ)^75) := mul_le_mul_of_nonneg_left hsq (by norm_num)
    _ ≤ _ := by norm_num

#print axioms positive_low_re_half
#print axioms low_paired_kernel_tiny
end WinnerDirectKernel
