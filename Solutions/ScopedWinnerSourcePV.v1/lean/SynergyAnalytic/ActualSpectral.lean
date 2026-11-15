import SynergyAnalytic.ExponentialLayer
import WinnerDensityA.Spectral
namespace SynergyAnalytic
open Complex Filter Topology Set MeasureTheory WinnerDensityA CH2QRH CH2.v7
set_option maxHeartbeats 0

/-- The actual weighted zero sum, with a continuous density envelope and
exact layer integral instead of a real-part grid. The powers of each actual
zero decrease as L grows; no monotonicity of L times an integral is assumed. -/
theorem actual_spectral_from_continuous_envelope
    (hrvm : ZeroCount.v1.rvm_error_bound) (hsmall : ZeroCount.v1.rvm_error_small)
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    {t x L0 : ℝ} (ht : 1000 ≤ t) (hx : 0 < x) (hL0 : 0 ≤ L0)
    (hL : L0 ≤ Real.log x) (hqrh : IEANTN.ZetaZeroFreeHalfPlane (7/8))
    (Q : ℝ→ℝ) (hQc : Continuous Q)
    (hQ : ∀s∈Icc (3/4:ℝ) (7/8),
      (2*Real.pi/t)*IEANTN.zetaZeroesSum (Ioo s 1) (Ioc 0 t)
        (fun ρ => t/Real.pi*(1/ρ.im)+2) ≤ Q s) :
    rawSpectral t x*x^((1:ℝ)/8)  ≤ 
      Real.exp (-Real.log x/8)*spectralBound t+pairedFunctional (7/8) (1/8) L0 Q := by
  classical
  have ht0 : 0 < t := by linarith
  have hp := Real.pi_pos
  have hlog : 0 ≤ Real.log x := hL0.trans hL
  have hfin := CH2Section7Z.finite_zeros_Ioc (a:=0) (b:=t) le_rfl
  let S := hfin.toFinset
  let w : ℂ → ℝ := fun ρ ↦ (2*Real.pi/t)*(t/Real.pi*(1/ρ.im)+2)*(IEANTN.zetaOrder ρ:ℝ)
  let B : ℂ → ℝ := fun ρ ↦ Real.exp (Real.log x*(ρ.re-7/8))
  let SH := S.filter (fun ρ ↦ (3/4:ℝ) < ρ.re)
  have hw : ∀ ρ ∈ S,0 ≤ w ρ := by
    intro ρ hρ
    have hh := (Set.Finite.mem_toFinset hfin).mp hρ
    have hi := hh.2.1.1
    have hm := CH2Section7Z.zetaOrder_nonneg_of_mem Set.Ioc_subset_Ioi_self hh
    dsimp [w]; positivity
  have hb : ∀ ρ ∈ S,ρ.re ≤ (7/8:ℝ) := by
    intro ρ hρ
    have hh := (Set.Finite.mem_toFinset hfin).mp hρ
    exact re_le_boundary hqrh hh.2.2 hh.2.1.1
  have hcumulative : ∀ σ : ℝ, (∑ ρ ∈ S,if σ < ρ.re then w ρ else 0) =
      (2*Real.pi/t)*IEANTN.zetaZeroesSum (Set.Ioo σ 1) (Set.Ioc 0 t)
        (fun ρ ↦ t/Real.pi*(1/ρ.im)+2) := by
    intro σ
    rw [←density_majorant_filter_eq,Finset.mul_sum]
    apply Finset.sum_congr rfl;intro ρ _
    dsimp [w]
    split_ifs  <;> ring
  have hhigh : ∀ σ : ℝ,(3/4:ℝ) ≤ σ →
      (∑ ρ ∈ SH,if σ < ρ.re then w ρ else 0)=∑ ρ ∈ S,if σ < ρ.re then w ρ else 0 := by
    intro σ hσ
    rw [show SH=S.filter (fun ρ ↦ (3/4:ℝ) < ρ.re) from rfl,Finset.sum_filter]
    apply Finset.sum_congr rfl;intro ρ _
    by_cases hi : σ < ρ.re
    · simp only [if_pos hi,if_pos (lt_of_le_of_lt hσ hi)]
    · simp only [if_neg hi,ite_self]
  have hbase : (∑ ρ ∈ SH,w ρ)  ≤  Q (3/4) := by
    have he : (∑ ρ ∈ SH,w ρ) =∑ ρ ∈ S,if (3/4:ℝ) < ρ.re then w ρ else 0 := by
      exact Finset.sum_filter ..
    rw [he,hcumulative]
    exact hQ (3/4) ⟨le_rfl,by norm_num⟩
  have hhighQ : ∀s∈Icc ((7/8:ℝ)-1/8) (7/8),
      (∑ρ∈SH,if s < ρ.re then w ρ else 0) ≤ Q s := by
    intro s hs
    rw [hhigh s (by linarith [hs.1]),hcumulative]
    exact hQ s ⟨by linarith [hs.1],hs.2⟩
  have hfinite := finite_exponential_envelope SH w Complex.re hL0
    (by norm_num : (0:ℝ) ≤ 1/8)
    (fun ρ hρ => hw ρ (Finset.mem_filter.mp hρ).1)
    (fun ρ hρ => hb ρ (Finset.mem_filter.mp hρ).1)
    (by simpa only [show (7/8:ℝ)-1/8=3/4 by norm_num] using hbase) hQc hhighQ
  have hhi : (∑ ρ ∈ SH,w ρ*B ρ)  ≤  pairedFunctional (7/8) (1/8) L0 Q := by
    apply (Finset.sum_le_sum (fun ρ hρ => ?_)).trans hfinite
    apply mul_le_mul_of_nonneg_left _ (hw ρ (Finset.mem_filter.mp hρ).1)
    apply Real.exp_le_exp.mpr
    have hr := hb ρ (Finset.mem_filter.mp hρ).1
    change Real.log x*(ρ.re-7/8)  ≤  L0*(ρ.re-7/8)
    nlinarith
  have hlo : (∑ ρ ∈ S,if ρ.re ≤ (3/4:ℝ) then w ρ*B ρ else 0)  ≤ 
      Real.exp (Real.log x*((3/4:ℝ)-7/8))*(∑ ρ ∈ S,w ρ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro ρ hρ
    by_cases hr : ρ.re ≤ (3/4:ℝ)
    · rw [if_pos hr]
      have he : B ρ ≤ Real.exp (Real.log x*((3/4:ℝ)-7/8)) := by
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_left (sub_le_sub_right hr _) hlog
      nlinarith [mul_le_mul_of_nonneg_left he (hw ρ hρ)]
    · rw [if_neg hr]
      exact mul_nonneg (Real.exp_pos _).le (hw ρ hρ)
  have hwtotal : (∑ ρ ∈ S,w ρ) ≤ spectralBound t := by
    have hh := mul_le_mul_of_nonneg_left (ordinate_majorant_sum_le hrvm hsmall hlow ht)
      (show 0 ≤ 2*Real.pi/t by positivity)
    have he : (∑ ρ ∈ S,w ρ)=(2*Real.pi/t)*IEANTN.zetaZeroesSum Set.univ (Set.Ioc 0 t)
        (fun ρ ↦ t/Real.pi*(1/ρ.im)+2) := by
      rw [CH2Section7Z.zetaZeroesSum_eq_sum hfin,Finset.mul_sum]
      apply Finset.sum_congr rfl;intro ρ _
      dsimp [w];ring
    rw [he]
    exact hh.trans_eq (by field_simp)
  have hlo' := hlo.trans (mul_le_mul_of_nonneg_left hwtotal (Real.exp_pos _).le)
  rw [show Real.log x*((3/4:ℝ)-7/8)=-Real.log x/8 by ring] at hlo'
  have hsplit : (∑ ρ ∈ S,w ρ*B ρ)=
      (∑ ρ ∈ S,if ρ.re ≤ (3/4:ℝ) then w ρ*B ρ else 0)+(∑ ρ ∈ SH,w ρ*B ρ) := by
    rw [show SH=S.filter (fun ρ ↦ (3/4:ℝ) < ρ.re) from rfl,Finset.sum_filter,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl;intro ρ _
    by_cases hr : ρ.re ≤ (3/4:ℝ)
    · rw [if_pos hr,if_neg (not_lt.mpr hr),add_zero]
    · rw [if_neg hr,if_pos (lt_of_not_ge hr),zero_add]
  have hraw : rawSpectral t x*x^((1:ℝ)/8)=∑ ρ ∈ S,w ρ*B ρ := by
    unfold rawSpectral
    rw [CH2Section7Z.zetaZeroesSum_eq_sum hfin,Finset.mul_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl;intro ρ _
    dsimp [w,B]
    rw [show ((2*Real.pi/t)*((t/Real.pi*(1/ρ.im)+2)*x^(ρ.re-1)*(IEANTN.zetaOrder ρ:ℝ)))*
        x^((1:ℝ)/8)=(2*Real.pi/t)*(t/Real.pi*(1/ρ.im)+2)*(IEANTN.zetaOrder ρ:ℝ)*
        (x^(ρ.re-1)*x^((1:ℝ)/8)) by ring,
      ←Real.rpow_add hx,Real.rpow_def_of_pos hx]
    congr 1;congr 1;ring
  rw [hraw,hsplit]
  exact add_le_add hlo' hhi

#print axioms actual_spectral_from_continuous_envelope
end SynergyAnalytic
