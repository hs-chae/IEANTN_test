import IEANTN.Vocabulary.PrimeCounting
import Mathlib
namespace RHContinuation.Ramanujan
open Real Set Filter MeasureTheory
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def liRegular (t : ℝ) : ℝ := 1/log t-1/(t-1)

lemma liRegular_bounds {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ liRegular t ∧ liRegular t ≤ 1 := by
  by_cases hz : t=0
  · subst t
    norm_num [liRegular]
  have ht0 : 0 < t := lt_of_le_of_ne ht (Ne.symm hz)
  by_cases h1 : t=1
  · subst t
    norm_num [liRegular]
  have hlne : log t ≠ 0 := log_ne_zero_of_pos_of_ne_one ht0 h1
  have htm : t-1 ≠ 0 := sub_ne_zero.mpr h1
  have hden : 0 < (t-1)*log t := by
    by_cases hh : 1 < t
    · exact mul_pos (sub_pos.mpr hh) (log_pos hh)
    · exact mul_pos_of_neg_of_neg (sub_neg.mpr (lt_of_le_of_ne (le_of_not_gt hh) h1))
        (log_neg ht0 (lt_of_le_of_ne (le_of_not_gt hh) h1))
  have hlo := log_le_sub_one_of_pos ht0
  have hup := mul_le_mul_of_nonneg_left (one_sub_inv_le_log_of_pos ht0) ht0.le
  have he : t*(1-t⁻¹)=t-1 := by field_simp
  rw [he] at hup
  have hrepr : liRegular t = (t-1-log t)/((t-1)*log t) := by
    unfold liRegular
    field_simp
    <;> ring
  rw [hrepr]
  constructor
  · exact div_nonneg (by linarith) hden.le
  · apply (div_le_one hden).mpr
    nlinarith


lemma liRegular_measurable : Measurable liRegular := by
  unfold liRegular
  fun_prop

lemma liRegular_integrable {x : ℝ} (hx : 0 ≤ x) :
    IntervalIntegrable liRegular volume 0 x := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hx]
  apply IntegrableOn.of_bound (by simpa only [Real.volume_Icc] using ENNReal.ofReal_lt_top)
    liRegular_measurable.aestronglyMeasurable (1:ℝ)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  rw [Real.norm_eq_abs,abs_of_nonneg (liRegular_bounds ht.1).1]
  exact (liRegular_bounds ht.1).2


noncomputable def liRegularPositive (t : ℝ) : ℝ :=
  if 0 ≤ t then liRegular t else 0

lemma liRegularPositive_measurable : Measurable liRegularPositive := by
  unfold liRegularPositive
  exact Measurable.ite measurableSet_Ici liRegular_measurable measurable_const

lemma liRegularPositive_norm (t : ℝ) : ‖liRegularPositive t‖ ≤ 1 := by
  by_cases ht : 0 ≤ t
  · simp only [liRegularPositive,if_pos ht,Real.norm_eq_abs,
      abs_of_nonneg (liRegular_bounds ht).1]
    exact (liRegular_bounds ht).2
  · simp [liRegularPositive,ht]

lemma liRegularPositive_integrable (a b : ℝ) :
    IntervalIntegrable liRegularPositive volume a b := by
  rw [intervalIntegrable_iff]
  apply IntegrableOn.of_bound (by simp [Real.volume_Ioc])
    liRegularPositive_measurable.aestronglyMeasurable (1:ℝ)
  exact Filter.Eventually.of_forall liRegularPositive_norm

noncomputable def liRegularPrimitive (b : ℝ) : ℝ :=
  ∫ t in (0:ℝ)..b, liRegularPositive t

lemma liRegularPrimitive_continuous : Continuous liRegularPrimitive :=
  intervalIntegral.continuous_primitive liRegularPositive_integrable 0

lemma li_truncation_domain {x ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hx : 1+ε ≤ x) :
    Ioc (0:ℝ) x \ Ioo (1-ε) (1+ε) = Ioc 0 (1-ε) ∪ Icc (1+ε) x := by
  ext t
  simp only [mem_diff,mem_Ioc,mem_Ioo,mem_union,mem_Icc]
  constructor
  · rintro ⟨⟨ht0,htx⟩,h⟩
    by_cases ht : t ≤ 1-ε
    · exact Or.inl ⟨ht0,ht⟩
    · exact Or.inr ⟨by push_neg at h;exact h (lt_of_not_ge ht),htx⟩
  · rintro (⟨ht0,ht1⟩|⟨ht1,htx⟩)
    · exact ⟨⟨ht0,by linarith⟩,by intro h;linarith [h.1]⟩
    · exact ⟨⟨by linarith,htx⟩,by intro h;linarith [h.2]⟩


lemma li_reassemble {t : ℝ} (ht : 0 ≤ t) :
    1/log t = liRegularPositive t+1/(t-1) := by
  simp only [liRegularPositive,ite_eq_left ht,liRegular]
  ring

lemma li_pole_left {ε : ℝ} (hε : 0 < ε) :
    (∫ t in (0:ℝ)..(1-ε), 1/(t-1)) = log ε := by
  rw [intervalIntegral.integral_comp_sub_right (fun t : ℝ => 1/t) 1]
  rw [integral_one_div_of_neg (by norm_num : (0:ℝ)-1<0) (by linarith : 1-ε-1<0)]
  congr 1
  ring

lemma li_pole_right {x ε : ℝ} (hε : 0 < ε) (hx : 1 < x) :
    (∫ t in (1+ε)..x, 1/(t-1)) = log (x-1)-log ε := by
  rw [intervalIntegral.integral_comp_sub_right (fun t : ℝ => 1/t) 1]
  rw [integral_one_div_of_pos (by linarith : 0<1+ε-1) (by linarith : 0<x-1)]
  rw [log_div (by linarith : x-1 ≠ 0) (by linarith : 1+ε-1 ≠ 0)]
  congr 1
  ring

lemma li_pole_left_integrable {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    IntervalIntegrable (fun t : ℝ => 1/(t-1)) volume 0 (1-ε) := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le (by linarith : (0:ℝ)≤1-ε)]
  apply continuousOn_const.div (continuousOn_id.sub continuousOn_const)
  intro t ht
  change t-1 ≠ 0
  linarith [ht.2]

lemma li_pole_right_integrable {x ε : ℝ} (hε : 0 < ε) (hx : 1+ε ≤ x) :
    IntervalIntegrable (fun t : ℝ => 1/(t-1)) volume (1+ε) x := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hx]
  apply continuousOn_const.div (continuousOn_id.sub continuousOn_const)
  intro t ht
  change t-1 ≠ 0
  linarith [ht.1]


lemma li_truncation_formula {x ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hx : 1+ε ≤ x) :
    (∫ t in Ioc (0:ℝ) x \ Ioo (1-ε) (1+ε), 1/log t) =
      liRegularPrimitive (1-ε)+liRegularPrimitive x-
        liRegularPrimitive (1+ε)+log (x-1) := by
  have ha : (0:ℝ) ≤ 1-ε := by linarith
  have hfrL : IntervalIntegrable (fun t : ℝ =>
      liRegularPositive t+1/(t-1)) volume 0 (1-ε) :=
    (liRegularPositive_integrable _ _).add (li_pole_left_integrable hε hε1)
  have hfrR : IntervalIntegrable (fun t : ℝ =>
      liRegularPositive t+1/(t-1)) volume (1+ε) x :=
    (liRegularPositive_integrable _ _).add (li_pole_right_integrable hε hx)
  have hfL : IntervalIntegrable (fun t : ℝ => 1/log t) volume 0 (1-ε) := by
    apply IntervalIntegrable.congr (f:=fun t : ℝ => liRegularPositive t+1/(t-1))
      (g:=fun t : ℝ => 1/log t) ?_ hfrL
    intro t ht
    rw [uIoc_of_le ha] at ht
    exact (li_reassemble ht.1.le).symm
  have hfR : IntervalIntegrable (fun t : ℝ => 1/log t) volume (1+ε) x := by
    apply IntervalIntegrable.congr (f:=fun t : ℝ => liRegularPositive t+1/(t-1))
      (g:=fun t : ℝ => 1/log t) ?_ hfrR
    intro t ht
    rw [uIoc_of_le hx] at ht
    exact (li_reassemble (by linarith [ht.1])).symm
  have hLset := (intervalIntegrable_iff_integrableOn_Ioc_of_le ha).mp hfL
  have hRset : IntegrableOn (fun t : ℝ => 1/log t) (Icc (1+ε) x) :=
    (integrableOn_Icc_iff_integrableOn_Ioc).mpr
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hx).mp hfR)
  have hdis : Disjoint (Ioc (0:ℝ) (1-ε)) (Icc (1+ε) x) := by
    rw [Set.disjoint_left]
    intro t ht ht'
    linarith [ht.2,ht'.1]
  rw [li_truncation_domain hε hε1 hx,
    setIntegral_union hdis measurableSet_Icc hLset hRset,
    integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le ha,
    ← intervalIntegral.integral_of_le hx]
  have heL : (∫ t in (0:ℝ)..(1-ε), 1/log t) =
      (∫ t in (0:ℝ)..(1-ε), liRegularPositive t)+log ε := by
    rw [intervalIntegral.integral_congr (g:=fun t : ℝ => liRegularPositive t+1/(t-1))
      (by intro t ht;rw [uIcc_of_le ha] at ht;exact li_reassemble ht.1)]
    rw [intervalIntegral.integral_add (liRegularPositive_integrable _ _)
      (li_pole_left_integrable hε hε1),li_pole_left hε]
  have heR : (∫ t in (1+ε)..x, 1/log t) =
      (∫ t in (1+ε)..x, liRegularPositive t)+log (x-1)-log ε := by
    rw [intervalIntegral.integral_congr (g:=fun t : ℝ => liRegularPositive t+1/(t-1))
      (by intro t ht;rw [uIcc_of_le hx] at ht;exact li_reassemble (by linarith [ht.1]))]
    rw [intervalIntegral.integral_add (liRegularPositive_integrable _ _)
      (li_pole_right_integrable hε hx),li_pole_right hε (by linarith)]
    ring
  rw [heL,heR]
  have hadj := intervalIntegral.integral_add_adjacent_intervals
    (liRegularPositive_integrable (0:ℝ) (1+ε)) (liRegularPositive_integrable (1+ε) x)
  change liRegularPrimitive (1+ε)+(∫ t in (1+ε)..x, liRegularPositive t)=
    liRegularPrimitive x at hadj
  change liRegularPrimitive (1-ε)+log ε+
    ((∫ t in (1+ε)..x, liRegularPositive t)+log (x-1)-log ε)=_
  linarith


/-- A direct regularization identity for the repository's actual principal-value
limit. No li existence, series identity, gamma identity or derivative is assumed. -/
theorem li_pv_regularization {x : ℝ} (hx : 1 < x) :
    IEANTN.li x = liRegularPrimitive x+log (x-1) := by
  let F := nhdsWithin (0:ℝ) (Ioi 0)
  have heps : Tendsto (fun ε : ℝ => ε) F (nhds 0) :=
    tendsto_id'.mpr nhdsWithin_le_nhds
  have hleft : Tendsto (fun ε : ℝ => 1-ε) F (nhds 1) := by
    convert tendsto_const_nhds.sub heps using 1 <;> simp
  have hright : Tendsto (fun ε : ℝ => 1+ε) F (nhds 1) := by
    convert tendsto_const_nhds.add heps using 1 <;> simp
  have hL := liRegularPrimitive_continuous.continuousAt.tendsto.comp hleft
  have hR := liRegularPrimitive_continuous.continuousAt.tendsto.comp hright
  have hsum := ((hL.add (tendsto_const_nhds (x:=liRegularPrimitive x))).sub hR).add
    (tendsto_const_nhds (x:=log (x-1)))
  have hsum' : Tendsto
      (fun ε : ℝ => liRegularPrimitive (1-ε)+liRegularPrimitive x-
        liRegularPrimitive (1+ε)+log (x-1)) F
      (nhds (liRegularPrimitive x+log (x-1))) := by
    simp only [Function.comp_def] at hsum
    convert hsum using 1 <;> first | rfl | ring
  have hsmall : {ε : ℝ | ε < min 1 (x-1)} ∈ F :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (lt_min (by norm_num) (by linarith)))
  have htrunc : Tendsto
      (fun ε : ℝ => ∫ t in Ioc (0:ℝ) x \ Ioo (1-ε) (1+ε), 1/log t)
      F (nhds (liRegularPrimitive x+log (x-1))) := by
    apply hsum'.congr'
    filter_upwards [self_mem_nhdsWithin,hsmall] with ε hε hsmall
    have hh := lt_min_iff.mp hsmall
    exact (li_truncation_formula hε hh.1 (by linarith [hh.2])).symm
  exact htrunc.limUnder_eq


lemma liRegularPositive_continuousAt {x : ℝ} (hx : 1 < x) :
    ContinuousAt liRegularPositive x := by
  have hx0 : x ≠ 0 := by linarith
  have hx1 : x-1 ≠ 0 := by linarith
  have hlog : log x ≠ 0 := (log_pos hx).ne'
  have hc : ContinuousAt liRegular x :=
    (continuousAt_const.div (Real.continuousAt_log hx0) hlog).sub
      (continuousAt_const.div (continuousAt_id.sub_const 1) hx1)
  have he : liRegularPositive =ᶠ[nhds x] liRegular := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    have hy0 : (0:ℝ) ≤ y := by
      have hy1 : (1:ℝ) < y := hy
      linarith
    exact if_pos hy0
  exact (continuousAt_congr he).mpr hc

/-- The derivative bridge is proved directly from the exact principal-value
`IEANTN.li` definition, including convergence of the symmetric truncations. -/
theorem actual_li_hasDerivAt {x : ℝ} (hx : 1 < x) :
    HasDerivAt IEANTN.li (1/log x) x := by
  have hg := intervalIntegral.integral_hasDerivAt_right
    (liRegularPositive_integrable 0 x)
    liRegularPositive_measurable.aestronglyMeasurable.stronglyMeasurableAtFilter
    (liRegularPositive_continuousAt hx)
  have hl := ((hasDerivAt_id x).sub_const 1).log (by linarith : x-1 ≠ 0)
  have hd := hg.add hl
  have hcoeff : liRegularPositive x+(x-1)⁻¹*1=1/log x := by
    simpa only [one_div,mul_one] using (li_reassemble (by linarith : (0:ℝ)≤x)).symm
  have hd' : HasDerivAt (fun y => liRegularPrimitive y+log (y-1)) (1/log x) x := by
    convert! hd using 1 <;> first | (simpa only [one_div,mul_one,id_eq] using hcoeff.symm) | rfl
  apply hd'.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hx] with y hy
  exact li_pv_regularization hy


/-- The principal-value and offset logarithmic integrals are connected on
exactly their common analytic domain, with the actual additive constant. -/
theorem actual_li_Li_offset {x : ℝ} (hx : 1 < x) :
    IEANTN.li x = IEANTN.Li x+IEANTN.li 2 := by
  have hmin : (1:ℝ) < min 2 x := lt_min (by norm_num) hx
  have hd : ∀ y ∈ uIcc (2:ℝ) x, HasDerivAt IEANTN.li (1/log y) y := by
    intro y hy
    exact actual_li_hasDerivAt (hmin.trans_le hy.1)
  have hc : ContinuousOn (fun y : ℝ => 1/log y) (uIcc (2:ℝ) x) := by
    apply continuousOn_const.div
    · apply Real.continuousOn_log.mono
      intro y hy
      exact ne_of_gt (by linarith [hmin.trans_le hy.1])
    · intro y hy
      exact (log_pos (hmin.trans_le hy.1)).ne'
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable
  unfold IEANTN.Li
  linarith


lemma log_pade_lower {t : ℝ} (ht : 1 ≤ t) :
    2*(t-1)/(t+1) ≤ log t := by
  let H : ℝ → ℝ := fun y => log y-2*(y-1)/(y+1)
  have hd : ∀ y ∈ Ici (1:ℝ), HasDerivAt H ((y-1)^2/(y*(y+1)^2)) y := by
    intro y hy
    have hy0 : y ≠ 0 := by linarith [hy.out]
    have hyp : y+1 ≠ 0 := by linarith [hy.out]
    have h := (Real.hasDerivAt_log hy0).sub
      ((((hasDerivAt_id y).sub_const 1).const_mul 2).div
        ((hasDerivAt_id y).add_const 1) hyp)
    convert! h using 1 <;> first | rfl | (dsimp [H];field_simp;ring)
  have hm : MonotoneOn H (Ici (1:ℝ)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici _)
    · intro y hy
      exact (hd y hy).continuousAt.continuousWithinAt
    · intro y hy
      exact (hd y (interior_subset hy)).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [(hd y (interior_subset hy)).deriv]
      have hy1 : (1:ℝ) ≤ y := interior_subset hy
      exact div_nonneg (sq_nonneg _) (mul_nonneg (by linarith) (sq_nonneg _))
  have h := hm (by simp) ht ht
  dsimp [H] at h
  norm_num at h
  linarith

lemma liRegularPositive_half {t : ℝ} (ht : 1 ≤ t) :
    liRegularPositive t ≤ 1/2 := by
  by_cases h1 : t=1
  · subst t
    norm_num [liRegularPositive,liRegular]
  have ht1 : 1 < t := lt_of_le_of_ne ht (Ne.symm h1)
  have hl : 0 < log t := log_pos ht1
  have htm : 0 < t-1 := by linarith
  have hp := (div_le_iff₀ (show (0:ℝ)<t+1 by linarith)).mp (log_pade_lower ht)
  have hr : liRegularPositive t = (t-1-log t)/((t-1)*log t) := by
    rw [liRegularPositive,if_pos (by linarith : (0:ℝ)≤t)]
    unfold liRegular
    field_simp
    <;> ring
  rw [hr]
  apply (div_le_iff₀ (mul_pos htm hl)).mpr
  nlinarith


lemma log_pade_upper {t : ℝ} (ht0 : 0 < t) (ht : t ≤ 1) :
    log t ≤ 2*(t-1)/(t+1) := by
  let H : ℝ → ℝ := fun y => log y-2*(y-1)/(y+1)
  have hd : ∀ y ∈ Icc t (1:ℝ), HasDerivAt H ((y-1)^2/(y*(y+1)^2)) y := by
    intro y hy
    have hy0 : y ≠ 0 := ne_of_gt (ht0.trans_le hy.1)
    have hyp : y+1 ≠ 0 := by linarith [ht0.trans_le hy.1]
    have h := (Real.hasDerivAt_log hy0).sub
      ((((hasDerivAt_id y).sub_const 1).const_mul 2).div
        ((hasDerivAt_id y).add_const 1) hyp)
    convert! h using 1 <;> first | rfl | (dsimp [H];field_simp;ring)
  have hm : MonotoneOn H (Icc t (1:ℝ)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · intro y hy
      exact (hd y hy).continuousAt.continuousWithinAt
    · intro y hy
      exact (hd y (interior_subset hy)).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [(hd y (interior_subset hy)).deriv]
      have hy0 : 0 < y := ht0.trans_le (interior_subset hy).1
      exact div_nonneg (sq_nonneg _) (mul_nonneg hy0.le (sq_nonneg _))
  have h := hm (by simp [ht]) (by simp [ht]) ht
  dsimp [H] at h
  norm_num at h
  linarith

lemma liRegularPositive_lower_half {t : ℝ} (ht0 : 0 < t) (ht : t < 1) :
    (1/2:ℝ) ≤ liRegularPositive t := by
  have hl : log t < 0 := log_neg ht0 ht
  have htm : t-1 < 0 := by linarith
  have hp := (le_div_iff₀ (show (0:ℝ)<t+1 by linarith)).mp (log_pade_upper ht0 ht.le)
  have hr : liRegularPositive t = (t-1-log t)/((t-1)*log t) := by
    rw [liRegularPositive,if_pos ht0.le]
    unfold liRegular
    field_simp [hl.ne,htm.ne]
    <;> ring
  rw [hr]
  apply (le_div_iff₀ (mul_pos_of_neg_of_neg htm hl)).mpr
  nlinarith

#print axioms li_truncation_formula
#print axioms li_pv_regularization
#print axioms actual_li_hasDerivAt
#print axioms actual_li_Li_offset
#print axioms liRegularPositive_half
#print axioms liRegularPositive_lower_half
end RHContinuation.Ramanujan
