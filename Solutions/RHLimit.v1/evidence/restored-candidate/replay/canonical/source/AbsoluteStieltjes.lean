/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import BPTZeroCount
import OcticFourier

/-! Smooth-majorant bridge for absolute Fourier zero sums. This avoids treating
abs(f) as continuously differentiable at its zeros. No numerical cap is assumed
or evaluated by this ordinary analytic proof. -/
namespace RHLimit.AbsoluteStieltjes
open Real Set MeasureTheory
open RHLimit.BPTZeroCount
set_option maxHeartbeats 0

noncomputable def smooth (ε : ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.sqrt ((f t) ^ 2 + ε ^ 2)
noncomputable def smoothDeriv (ε : ℝ) (f f' : ℝ → ℝ) (t : ℝ) : ℝ :=
  f t * f' t / Real.sqrt ((f t) ^ 2 + ε ^ 2)

lemma smooth_pos {ε : ℝ} (hε : 0 < ε) (f : ℝ → ℝ) (t : ℝ) :
    0 < smooth ε f t := by
  unfold smooth
  apply Real.sqrt_pos.mpr
  nlinarith [sq_nonneg (f t)]

lemma smooth_lower (ε : ℝ) (f : ℝ → ℝ) (t : ℝ) : |f t| ≤ smooth ε f t := by
  exact Real.abs_le_sqrt (by nlinarith [sq_nonneg ε])

lemma smooth_upper {ε : ℝ} (hε : 0 ≤ ε) (f : ℝ → ℝ) (t : ℝ) :
    smooth ε f t ≤ |f t| + ε := by
  apply (Real.sqrt_le_left (by positivity : 0 ≤ |f t| + ε)).mpr
  nlinarith [sq_abs (f t), abs_nonneg (f t), mul_nonneg (abs_nonneg (f t)) hε]

lemma smooth_derivative {ε t : ℝ} (hε : 0 < ε) {f : ℝ → ℝ} {f' : ℝ}
    (hf : HasDerivAt f f' t) :
    HasDerivAt (smooth ε f) (f t * f' / Real.sqrt ((f t) ^ 2 + ε ^ 2)) t := by
  have hs : (f t) ^ 2 + ε ^ 2 ≠ 0 := by nlinarith [sq_nonneg (f t)]
  apply (((hf.pow 2).add_const (ε ^ 2)).sqrt hs).congr_deriv
  norm_num
  ring

lemma smooth_derivative_bound {ε : ℝ} (hε : 0 < ε) (f f' : ℝ → ℝ) (t : ℝ) :
    |smoothDeriv ε f f' t| ≤ |f' t| := by
  have hs := smooth_pos hε f t
  have hlo := smooth_lower ε f t
  change |f t * f' t / smooth ε f t| ≤ _
  rw [abs_div, abs_mul, abs_of_pos hs]
  apply (div_le_iff₀ hs).mpr
  nlinarith [mul_le_mul_of_nonneg_right hlo (abs_nonneg (f' t))]

lemma smooth_continuousOn {s : Set ℝ} {ε : ℝ} {f : ℝ → ℝ}
    (hf : ContinuousOn f s) : ContinuousOn (smooth ε f) s :=
  ((hf.pow 2).add continuousOn_const).sqrt

lemma smoothDeriv_continuousOn {s : Set ℝ} {ε : ℝ} (hε : 0 < ε)
    {f f' : ℝ → ℝ} (hf : ContinuousOn f s) (hf' : ContinuousOn f' s) :
    ContinuousOn (smoothDeriv ε f f') s :=
  (hf.mul hf').div (smooth_continuousOn hf) (fun t _ => (smooth_pos hε f t).ne')

lemma density_nonneg {t : ℝ} (ht : 2 * Real.pi ≤ t) : 0 ≤ density t := by
  unfold density
  apply div_nonneg _ (by positivity)
  apply Real.log_nonneg
  exact (le_div_iff₀ (by positivity : 0 < 2 * Real.pi)).mpr (by simpa using ht)

/-- Finite absolute-value estimate with an explicit vanishing smooth-majorant error. -/
lemma majorant_bound (h : PublishedBound) {a b ε : ℝ}
    (ha : 2 * Real.pi ≤ a) (hab : a ≤ b) (hε : 0 < ε) {f f' : ℝ → ℝ}
    (hd : ∀ t ∈ uIcc a b, HasDerivAt f (f' t) t)
    (hc : ContinuousOn f' (uIcc a b)) :
    IEANTN.zetaZeroesSum Set.univ (Set.Ioc a b) (fun ρ ↦ |f ρ.im|) ≤
      (∫ t in a..b, |f t| * density t) +
      (7 / 25) * (|f b| * Real.log b + |f a| * Real.log a +
        ∫ t in a..b, |f' t| * Real.log t) +
      ε * ((∫ t in a..b, density t) + (7 / 25) * (Real.log b + Real.log a)) := by
  have ha0 : 0 < a := by linarith [Real.pi_pos]
  have hp (t : ℝ) (ht : t ∈ uIcc a b) : 0 < t := by
    rw [uIcc_of_le hab] at ht
    exact ha0.trans_le ht.1
  have hfc : ContinuousOn f (uIcc a b) :=
    fun t ht => (hd t ht).continuousAt.continuousWithinAt
  have hgc := smooth_continuousOn (ε := ε) hfc
  have hgdc := smoothDeriv_continuousOn hε hfc hc
  have hgd : ∀ t ∈ uIcc a b,
      HasDerivAt (smooth ε f) (smoothDeriv ε f f' t) t := by
    intro t ht
    exact smooth_derivative hε (hd t ht)
  have hdensity : ContinuousOn density (uIcc a b) := by
    unfold density
    apply ContinuousOn.div_const
    apply ContinuousOn.log (continuousOn_id.div_const (2 * Real.pi))
    intro t ht
    exact div_ne_zero (hp t ht).ne' (by positivity)
  have hlog : ContinuousOn Real.log (uIcc a b) :=
    fun t ht => (Real.continuousAt_log (hp t ht).ne').continuousWithinAt
  have hlog0 (t : ℝ) (ht : a ≤ t) : 0 ≤ Real.log t := by
    apply Real.log_nonneg
    linarith [Real.pi_gt_three]
  have hsum : IEANTN.zetaZeroesSum Set.univ (Set.Ioc a b) (fun ρ ↦ |f ρ.im|) ≤
      IEANTN.zetaZeroesSum Set.univ (Set.Ioc a b) (fun ρ ↦ smooth ε f ρ.im) := by
    let hz := CH2Section7Z.finite_zeros_Ioc (a := a) (b := b) ha0.le
    rw [CH2Section7Z.zetaZeroesSum_eq_sum hz, CH2Section7Z.zetaZeroesSum_eq_sum hz]
    apply Finset.sum_le_sum
    intro ρ hρ
    exact mul_le_mul_of_nonneg_right (smooth_lower ε f ρ.im)
      (CH2Section7Z.zetaOrder_nonneg_of_mem (fun t ht => ha0.trans ht.1)
        ((Set.Finite.mem_toFinset hz).mp hρ))
  have hmain : (∫ t in a..b, smooth ε f t * density t) ≤
      (∫ t in a..b, |f t| * density t) + ε * ∫ t in a..b, density t := by
    calc _ ≤ ∫ t in a..b, (|f t| + ε) * density t := by
           apply intervalIntegral.integral_mono_on hab (hgc.mul hdensity).intervalIntegrable
             ((hfc.abs.add continuousOn_const).mul hdensity).intervalIntegrable
           intro t ht
           exact mul_le_mul_of_nonneg_right (smooth_upper hε.le f t)
             (density_nonneg (ha.trans ht.1))
         _ = _ := by
           simp only [add_mul]
           rw [intervalIntegral.integral_add, intervalIntegral.integral_const_mul]
           · exact (hfc.abs.mul hdensity).intervalIntegrable
           · exact (hdensity.const_mul ε).intervalIntegrable
  have hder : (∫ t in a..b, |smoothDeriv ε f f' t| * Real.log t) ≤
      ∫ t in a..b, |f' t| * Real.log t := by
    apply intervalIntegral.integral_mono_on hab (hgdc.abs.mul hlog).intervalIntegrable
      (hc.abs.mul hlog).intervalIntegrable
    intro t ht
    exact mul_le_mul_of_nonneg_right (smooth_derivative_bound hε f f' t) (hlog0 t ht.1)
  have hb := mul_le_mul_of_nonneg_right (smooth_upper hε.le f b) (hlog0 b hab)
  have haa := mul_le_mul_of_nonneg_right (smooth_upper hε.le f a) (hlog0 a le_rfl)
  have he := (le_abs_self _).trans (finite_remainder_bound h ha hab hgd hgdc)
  rw [abs_of_pos (smooth_pos hε f b), abs_of_pos (smooth_pos hε f a)] at he
  nlinarith

/-- The actual finite absolute-value Stieltjes bound, without differentiability of abs(f). -/
theorem finite_absolute_bound (h : PublishedBound) {a b : ℝ}
    (ha : 2 * Real.pi ≤ a) (hab : a ≤ b) {f f' : ℝ → ℝ}
    (hd : ∀ t ∈ uIcc a b, HasDerivAt f (f' t) t)
    (hc : ContinuousOn f' (uIcc a b)) :
    IEANTN.zetaZeroesSum Set.univ (Set.Ioc a b) (fun ρ ↦ |f ρ.im|) ≤
      (∫ t in a..b, |f t| * density t) +
      (7 / 25) * (|f b| * Real.log b + |f a| * Real.log a +
        ∫ t in a..b, |f' t| * Real.log t) := by
  apply le_of_forall_pos_le_add
  intro η hη
  let A := (∫ t in a..b, density t) + (7 / 25) * (Real.log b + Real.log a)
  let ε := η / (|A| + 1)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have he := majorant_bound h ha hab hε hd hc
  have hslack : ε * A ≤ η := by
    calc _ ≤ ε * (|A| + 1) :=
           mul_le_mul_of_nonneg_left (by linarith [le_abs_self A]) hε.le
         _ = η := by dsimp [ε]; field_simp
  exact he.trans (by dsimp [A] at hslack; linarith)

noncomputable def octicPacket (δ t : ℝ) : ℝ := δ * EvenKernel.transform 4 (δ * t)
noncomputable def octicPacketDeriv (δ t : ℝ) : ℝ :=
  δ ^ 2 * RHLimit.OcticFourier.formulaDerivative (δ * t)

lemma octicPacket_derivative {δ t : ℝ} (hδ : 0 < δ) (ht : 0 < t) :
    HasDerivAt (octicPacket δ) (octicPacketDeriv δ t) t := by
  have hne : δ * t ≠ 0 := mul_ne_zero hδ.ne' ht.ne'
  have hh := ((RHLimit.OcticFourier.transform_hasDerivAt hne).comp t
    ((hasDerivAt_id t).const_mul δ)).const_mul δ
  apply hh.congr_deriv
  dsimp [octicPacketDeriv]
  ring

lemma octicPacketDeriv_continuousOn {δ a b : ℝ} (hδ : 0 < δ)
    (ha : 0 < a) (hab : a ≤ b) : ContinuousOn (octicPacketDeriv δ) (uIcc a b) := by
  intro t ht
  rw [uIcc_of_le hab] at ht
  have ht0 : t ≠ 0 := (ha.trans_le ht.1).ne'
  have hne : δ * t ≠ 0 := mul_ne_zero hδ.ne' ht0
  apply ContinuousAt.continuousWithinAt
  unfold octicPacketDeriv RHLimit.OcticFourier.formulaDerivative
  fun_prop (disch := aesop)

/-- The finite absolute weighted estimate attached to the actual scaled octic kernel.
No Fourier identity or regularity premise remains in this specialized theorem. -/
theorem octic_finite_bound (h : PublishedBound) {δ a b : ℝ} (hδ : 0 < δ)
    (ha : 2 * Real.pi ≤ a) (hab : a ≤ b) :
    IEANTN.zetaZeroesSum Set.univ (Set.Ioc a b) (fun ρ ↦ |octicPacket δ ρ.im|) ≤
      (∫ t in a..b, |octicPacket δ t| * density t) +
      (7 / 25) * (|octicPacket δ b| * Real.log b + |octicPacket δ a| * Real.log a +
        ∫ t in a..b, |octicPacketDeriv δ t| * Real.log t) := by
  have ha0 : 0 < a := by linarith [Real.pi_pos]
  apply finite_absolute_bound h ha hab
    (f' := octicPacketDeriv δ) _ (octicPacketDeriv_continuousOn hδ ha0 hab)
  intro t ht
  rw [uIcc_of_le hab] at ht
  exact octicPacket_derivative hδ (ha0.trans_le ht.1)

#print axioms smooth_derivative_bound
#print axioms finite_absolute_bound
#print axioms octic_finite_bound
end RHLimit.AbsoluteStieltjes
