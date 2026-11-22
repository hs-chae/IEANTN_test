import ActualAnchors
import AnalyticBridges
namespace RHContinuation.Ramanujan
open Real Set IEANTN RamanujanPV.AnalyticTransition
open Ramanujan640 Ramanujan640.AnalyticBarrier
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def globalActual (z : ℝ) : ℝ :=
  (8/5:ℝ)*exp z/z-IEANTN.li (exp z)

lemma anchor_eight_thirds_upper :
    IEANTN.li (exp (8/3:ℝ)) ≤ (3/5:ℝ)*exp (8/3:ℝ) := by
  have hb := actual_li_exp_bounds155 (z:=(8/3:ℝ)) (L:=0) (H:=1)
    (by norm_num) (by norm_num) (by
      constructor
      · exact log_nonneg (by norm_num)
      · have h : log (8/3:ℝ) ≤ 1 := by interval_decide 80 (trust := kernel)
        exact h)
  have he := exp_bounds155 (z:=(8/3:ℝ)) (by norm_num) (by norm_num)
  have hn : wideEiHi (8/3:ℝ) 1 ≤ (3/5:ℝ)*expPartial155 (8/3:ℝ) := by
    norm_num [wideEiHi,eiPartial155,eiTerm,expPartial155,expTerm,
      Finset.sum_range_succ,Nat.factorial]
  linarith [he.1]

theorem globalActual_hasDerivAt {z : ℝ} (hz : 0 < z) :
    HasDerivAt (globalActual) (exp z*(3*z-8)/(5*z^2)) z := by
  have hz0 : z ≠ 0 := hz.ne'
  have hli := (actual_li_hasDerivAt (x:=exp z) (by simpa using Real.one_lt_exp_iff.mpr hz)).comp z
    (Real.hasDerivAt_exp z)
  have h := (((Real.hasDerivAt_exp z).const_mul (8/5:ℝ)).div
    (hasDerivAt_id z) hz0).sub hli
  convert! h using 1 <;> first | rfl | skip
  simp only [Function.comp_apply,id_eq,Real.log_exp]
  field_simp
  <;> ring

/-- The global3/2 bound used in the frozen prime-power transport.
The sole non-computational assumptions are named standard li identities. -/
theorem actual_w_le_eight_fifths
    {z : ℝ} (hz : 0 < z) : w IEANTN.li z ≤ 8/5 := by
  have hbase : 0 ≤ globalActual (8/3) := by
    have h := anchor_eight_thirds_upper
    dsimp [globalActual]
    norm_num only [div_eq_mul_inv] at *
    nlinarith
  have hcompare : globalActual (8/3) ≤ globalActual z := by
    by_cases hz3 : z ≤ (8/3:ℝ)
    · have hdI : ∀ t ∈ Icc z (8/3:ℝ),
          HasDerivAt (globalActual) (exp t*(3*t-8)/(5*t^2)) t := by
        intro t ht
        exact globalActual_hasDerivAt (hz.trans_le ht.1)
      have hm : AntitoneOn (globalActual) (Icc z (8/3:ℝ)) := by
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
    · have hdI : ∀ t ∈ Ici (8/3:ℝ),
          HasDerivAt (globalActual) (exp t*(3*t-8)/(5*t^2)) t := by
        intro t ht
        exact globalActual_hasDerivAt (by linarith [ht.out])
      have hm : MonotoneOn (globalActual) (Ici (8/3:ℝ)) := by
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
  have hbound : IEANTN.li (exp z) ≤ (8/5:ℝ)*exp z/z := by
    dsimp [globalActual] at hnonneg
    linarith
  have h := mul_le_mul_of_nonneg_left hbound (show 0 ≤ z*exp (-z) by positivity)
  have he : exp z ≠ 0 := exp_ne_zero z
  have hz0 : z ≠ 0 := hz.ne'
  change z*(exp (-z)*IEANTN.li (exp z)) ≤ 8/5
  have heq : z*exp (-z)*((8/5:ℝ)*exp z/z) = 8/5 := by
    rw [Real.exp_neg]
    field_simp
  rw [heq] at h
  nlinarith


#print axioms anchor_eight_thirds_upper
#print axioms actual_w_le_eight_fifths
end RHContinuation.Ramanujan
