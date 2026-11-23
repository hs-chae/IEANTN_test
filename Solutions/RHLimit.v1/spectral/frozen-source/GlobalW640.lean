import Anchor640

namespace Ramanujan640.AnalyticBarrier
open Real Set Finset RamanujanPV.AnalyticTransition
set_option maxHeartbeats 0
set_option maxRecDepth 10000

/-- The same standard derivative law, stated on its actual full analytic
domain x>1 rather than the old application's narrower x>2 contract. -/
def LiDerivativeFromOne (li : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, 1 < x → HasDerivAt li (1/log x) x

noncomputable def globalUpperDifference (li : ℝ → ℝ) (z : ℝ) : ℝ :=
  (3/2:ℝ)*exp z/z-li (exp z)

theorem globalUpperDifference_hasDerivAt {li : ℝ → ℝ}
    (hd : LiDerivativeFromOne li) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (globalUpperDifference li) (exp z*(z-3)/(2*z^2)) z := by
  have hz0 : z ≠ 0 := hz.ne'
  have hli := (hd (exp z) (by simpa using Real.one_lt_exp_iff.mpr hz)).comp z
    (Real.hasDerivAt_exp z)
  have h := (((Real.hasDerivAt_exp z).const_mul (3/2:ℝ)).div
    (hasDerivAt_id z) hz0).sub hli
  convert! h using 1 <;> first | rfl | skip
  simp only [Function.comp_apply,id_eq,Real.log_exp]
  field_simp
  <;> ring

/-- The global3/2 bound used in the frozen prime-power transport.
The sole non-computational assumptions are named standard li identities. -/
theorem actual_w_le_three_halves {li : ℝ → ℝ}
    (hseries : LogIntegralSeriesIdentity li) (hd : LiDerivativeFromOne li)
    {z : ℝ} (hz : 0 < z) : w li z ≤ 3/2 := by
  have hbase : 0 ≤ globalUpperDifference li 3 := by
    have h := anchor3_upper hseries
    dsimp [globalUpperDifference]
    nlinarith
  have hcompare : globalUpperDifference li 3 ≤ globalUpperDifference li z := by
    by_cases hz3 : z ≤ 3
    · have hdI : ∀ t ∈ Icc z 3,
          HasDerivAt (globalUpperDifference li) (exp t*(t-3)/(2*t^2)) t := by
        intro t ht
        exact globalUpperDifference_hasDerivAt hd (hz.trans_le ht.1)
      have hm : AntitoneOn (globalUpperDifference li) (Icc z 3) := by
        apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
        · intro t ht
          exact (hdI t ht).continuousAt.continuousWithinAt
        · intro t ht
          exact (hdI t (interior_subset ht)).differentiableAt.differentiableWithinAt
        · intro t ht
          rw [(hdI t (interior_subset ht)).deriv]
          have hh := interior_subset ht
          exact div_nonpos_of_nonpos_of_nonneg
            (mul_nonpos_of_nonneg_of_nonpos (exp_pos t).le (by linarith [hh.2]))
            (by positivity)
      exact hm ⟨le_refl _,hz3⟩ ⟨hz3,le_refl _⟩ hz3
    · have hdI : ∀ t ∈ Ici (3:ℝ),
          HasDerivAt (globalUpperDifference li) (exp t*(t-3)/(2*t^2)) t := by
        intro t ht
        exact globalUpperDifference_hasDerivAt hd (by linarith [ht.out])
      have hm : MonotoneOn (globalUpperDifference li) (Ici (3:ℝ)) := by
        apply monotoneOn_of_deriv_nonneg (convex_Ici _)
        · intro t ht
          exact (hdI t ht).continuousAt.continuousWithinAt
        · intro t ht
          exact (hdI t (interior_subset ht)).differentiableAt.differentiableWithinAt
        · intro t ht
          rw [(hdI t (interior_subset ht)).deriv]
          have hh := interior_subset ht
          exact div_nonneg (mul_nonneg (exp_pos t).le (by linarith [hh.out]))
            (by positivity)
      exact hm (by simp) (le_of_not_ge hz3) (le_of_not_ge hz3)
  have hnonneg := hbase.trans hcompare
  have hbound : li (exp z) ≤ (3/2:ℝ)*exp z/z := by
    dsimp [globalUpperDifference] at hnonneg
    linarith
  have h := mul_le_mul_of_nonneg_left hbound (show 0 ≤ z*exp (-z) by positivity)
  have he : exp z ≠ 0 := exp_ne_zero z
  have hz0 : z ≠ 0 := hz.ne'
  change z*(exp (-z)*li (exp z)) ≤ 3/2
  have heq : z*exp (-z)*((3/2:ℝ)*exp z/z) = 3/2 := by
    rw [Real.exp_neg]
    field_simp
  rw [heq] at h
  nlinarith

#print axioms globalUpperDifference_hasDerivAt
#print axioms actual_w_le_three_halves
end Ramanujan640.AnalyticBarrier
