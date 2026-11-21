import RealCrossing
open Real Set RamanujanPV RamanujanPV.AnalyticTransition
namespace CrossingBracket
set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option Elab.async false

theorem log_bounds {r l u U : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (hl : l ≤ logAtanhPoly 20 r) (hu : logAtanhPoly 20 r ≤ u)
    (hU : u + 2*r^41/(41*(1-r^2)) ≤ U) :
    l ≤ log ((1+r)/(1-r)) ∧ log ((1+r)/(1-r)) ≤ U := by
  have hh := log_atanh20_error hr hr1
  unfold logAtanhError at hh
  rw [log_div (by linarith) (by linarith)]
  constructor <;> linarith

theorem log_two :
    (69314718055994530941573/100000000000000000000000:ℝ) ≤ log ((1+(1/3:ℝ))/(1-(1/3:ℝ))) ∧
      log ((1+(1/3:ℝ))/(1-(1/3:ℝ))) ≤ (69314718055994530941727/100000000000000000000000:ℝ) := by
  apply log_bounds (u := (34657359027997265470787/50000000000000000000000:ℝ)) (by norm_num) (by norm_num)
  · norm_num [logAtanhPoly, Finset.sum_range_succ]
  · norm_num [logAtanhPoly, Finset.sum_range_succ]
  · norm_num

theorem log_lo :
    (2752486666237341375447/25000000000000000000000:ℝ) ≤ log ((1+(1999549657108963/36359288025108963:ℝ))/(1-(1999549657108963/36359288025108963:ℝ))) ∧
      log ((1+(1999549657108963/36359288025108963:ℝ))/(1-(1999549657108963/36359288025108963:ℝ))) ≤ (11009946664949365501791/100000000000000000000000:ℝ) := by
  apply log_bounds (u := (11009946664949365501789/100000000000000000000000:ℝ)) (by norm_num) (by norm_num)
  · norm_num [logAtanhPoly, Finset.sum_range_succ]
  · norm_num [logAtanhPoly, Finset.sum_range_succ]
  · norm_num

theorem log_hi :
    (11009946664949368108749/100000000000000000000000:ℝ) ≤ log ((1+(3999099314217927/72718576050217927:ℝ))/(1-(3999099314217927/72718576050217927:ℝ))) ∧
      log ((1+(3999099314217927/72718576050217927:ℝ))/(1-(3999099314217927/72718576050217927:ℝ))) ≤ (688121666559335506797/6250000000000000000000:ℝ) := by
  apply log_bounds (u := (8807957331959494487/80000000000000000000:ℝ)) (by norm_num) (by norm_num)
  · norm_num [logAtanhPoly, Finset.sum_range_succ]
  · norm_num [logAtanhPoly, Finset.sum_range_succ]
  · norm_num

theorem log_x_lo : (2437025078624757948456843/100000000000000000000000:ℝ) ≤ log (19179418841108963/500000:ℝ) ∧
    log (19179418841108963/500000:ℝ) ≤ (609256269656189487115559/25000000000000000000000:ℝ) := by
  have h1 := log_two
  rw [show (1+(1/3:ℝ))/(1-(1/3:ℝ))=(2:ℝ) by norm_num] at h1
  have h2 := log_lo
  have he : log (19179418841108963/500000:ℝ) = (35:ℝ)*log 2+log ((1+(1999549657108963/36359288025108963:ℝ))/(1-(1999549657108963/36359288025108963:ℝ))) := by
    rw [show (35:ℝ)=((35:ℕ):ℝ) by norm_num, ← Real.log_pow, ← Real.log_mul (by norm_num) (by norm_num)]
    congr 1
    norm_num
  rw [he]
  constructor <;> linarith [h1.1,h1.2,h2.1,h2.2]

theorem log_x_hi : (609256269656189487765951/25000000000000000000000:ℝ) ≤ log (38358837682217927/1000000:ℝ) ∧
    log (38358837682217927/1000000:ℝ) ≤ (2437025078624757951069197/100000000000000000000000:ℝ) := by
  have h1 := log_two
  rw [show (1+(1/3:ℝ))/(1-(1/3:ℝ))=(2:ℝ) by norm_num] at h1
  have h2 := log_hi
  have he : log (38358837682217927/1000000:ℝ) = (35:ℝ)*log 2+log ((1+(3999099314217927/72718576050217927:ℝ))/(1-(3999099314217927/72718576050217927:ℝ))) := by
    rw [show (35:ℝ)=((35:ℕ):ℝ) by norm_num, ← Real.log_pow, ← Real.log_mul (by norm_num) (by norm_num)]
    congr 1
    norm_num
  rw [he]
  constructor <;> linarith [h1.1,h1.2,h2.1,h2.2]


theorem e_from_source :
    (3133965575612453533:ℝ)/(2:ℝ)^60 ≤ exp 1 ∧
      exp 1 ≤ (3133965575612453555:ℝ)/(2:ℝ)^60 := by
  let heap : QuotientCMachine.Heap := fun _ ↦ none
  exact FiniteExpLinked.source_outputs_enclose_e
     (FiniteExpExecute.low_function_executes heap) (FiniteExpLinked.linked_high_executes heap)

theorem sign_lo : gap (19179418841108963/500000:ℝ) < 0 := by
  have hx : (19179418841108963/500000:ℝ) ∈ Icc RealCrossing.A RealCrossing.B := by norm_num [RealCrossing.A,RealCrossing.B]
  rw [RealCrossing.on_unit hx]
  unfold RealCrossing.f
  rw [sub_neg,div_mul_eq_mul_div]
  have hp := lt_of_lt_of_le (by norm_num : 0 < (2437025078624757948456843/100000000000000000000000:ℝ)) log_x_lo.1
  apply (div_lt_iff₀ hp).2
  have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right e_from_source.2
    (show 0 ≤ (19179418841108963/500000:ℝ) by norm_num)) (show (0:ℝ) ≤ 632207037 by norm_num)
  have h2 := mul_le_mul_of_nonneg_left log_x_lo.1 (sq_nonneg (1644673232:ℝ))
  exact h.trans_lt ((by norm_num : (3133965575612453555:ℝ)/(2:ℝ)^60*(19179418841108963/500000:ℝ)*632207037 <
    (1644673232:ℝ)^2*(2437025078624757948456843/100000000000000000000000:ℝ)).trans_le h2)

theorem sign_hi : 0 < gap (38358837682217927/1000000:ℝ) := by
  have hx : (38358837682217927/1000000:ℝ) ∈ Icc RealCrossing.A RealCrossing.B := by norm_num [RealCrossing.A,RealCrossing.B]
  rw [RealCrossing.on_unit hx]
  unfold RealCrossing.f
  rw [sub_pos,div_mul_eq_mul_div]
  have hp : 0 < log (38358837682217927/1000000:ℝ) := by apply Real.log_pos; norm_num
  apply (lt_div_iff₀ hp).2
  have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right e_from_source.1
    (show 0 ≤ (38358837682217927/1000000:ℝ) by norm_num)) (show (0:ℝ) ≤ 632207037 by norm_num)
  have h2 := mul_le_mul_of_nonneg_left log_x_hi.2 (sq_nonneg (1644673232:ℝ))
  exact h2.trans_lt ((by norm_num : (1644673232:ℝ)^2*(2437025078624757951069197/100000000000000000000000:ℝ) <
    (3133965575612453533:ℝ)/(2:ℝ)^60*(38358837682217927/1000000:ℝ)*632207037).trans_le h)

theorem root_in_bracket :
    ∃ z ∈ Ioo (19179418841108963/500000:ℝ) (38358837682217927/1000000:ℝ), gap z = 0 ∧
      ∀ x ∈ Icc RealCrossing.A RealCrossing.B, 0 < gap x ↔ z < x := by
  obtain ⟨z,hz,hzg,hp⟩ := RealCrossing.zero_in_unit
  have hLeft : (19179418841108963/500000:ℝ) ∈ Icc RealCrossing.A RealCrossing.B := by norm_num [RealCrossing.A,RealCrossing.B]
  have hRight : (38358837682217927/1000000:ℝ) ∈ Icc RealCrossing.A RealCrossing.B := by norm_num [RealCrossing.A,RealCrossing.B]
  have hl : (19179418841108963/500000:ℝ) < z := by
    by_contra! hn
    rcases eq_or_lt_of_le hn with he | hh
    · have h := sign_lo
      rw [←he,hzg] at h
      exact (lt_irrefl 0) h
    · exact (not_lt_of_gt sign_lo) ((hp _ hLeft).mpr hh)
  exact ⟨z,⟨hl,(hp _ hRight).mp sign_hi⟩,hzg,hp⟩

#print axioms root_in_bracket
end CrossingBracket
