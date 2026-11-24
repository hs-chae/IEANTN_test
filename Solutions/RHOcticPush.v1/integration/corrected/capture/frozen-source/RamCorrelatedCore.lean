import RamPushCore
import GMPair

/-! Preserve the correlation between the two actual compensated J-errors.
The shared integral is cancelled before taking absolute values. This is an
actual prime-counting consumer of the proved GM pair theorem, not an assumed
improved single-height spectral constant. -/
namespace RHOcticPush.Correlated
open Real Set Finset IEANTN RamanujanPV.AnalyticTransition
open Ramanujan640 Ramanujan640.AnalyticBarrier RHContinuation.Ramanujan
open RHLimit.Ram620 RHOcticPush.Ram
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

noncomputable def F (z : ℝ) : ℝ := z^4*exp (-z/2)
noncomputable def H (z : ℝ) : ℝ := z^5/(z-1)*exp ((1-z)/2)
noncomputable def Q (z : ℝ) : ℝ := z^4*exp (-z)
noncomputable def T (z : ℝ) : ℝ := z^5*exp (-z)

lemma deficit_error {z : ℝ} (hz : z ≠ 0) :
    deficit z = psiDeficit z+primePart z-z/exp (z/2)*GM.error (exp z) := by
  unfold deficit psiDeficit primePart GM.error
  rw [Real.log_exp]
  field_simp [hz,exp_ne_zero]
  ring

lemma F_error (z : ℝ) : F z*(z/exp (z/2))=T z := by
  calc
    F z*(z/exp (z/2)) = z^5*(exp (-z/2)/exp (z/2)) := by
      unfold F
      ring
    _ = T z := by
      rw [←Real.exp_sub]
      unfold T
      congr 2 <;> ring

lemma H_error {z : ℝ} (hz : z ≠ 1) :
    H z*((z-1)/exp ((z-1)/2))=T z*exp 1 := by
  calc
    H z*((z-1)/exp ((z-1)/2)) =
        z^5*(exp ((1-z)/2)/exp ((z-1)/2)) := by
      unfold H
      field_simp [show z-1 ≠ 0 by exact sub_ne_zero.mpr hz]
    _ = z^5*exp (1-z) := by
      rw [←Real.exp_sub]
      congr 2 <;> ring
    _ = T z*exp 1 := by
      unfold T
      rw [mul_assoc,←Real.exp_add]
      congr 2 <;> ring

lemma linear_identity {k z : ℝ} (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    k*F z*deficit z-H z*deficit (z-1) =
      k*F z*(psiDeficit z+primePart z)-H z*(psiDeficit (z-1)+primePart (z-1))-
        T z*(k*GM.error (exp z)-exp 1*GM.error (exp (z-1))) := by
  rw [deficit_error hz0,deficit_error (sub_ne_zero.mpr hz1)]
  calc
    _ = k*F z*(psiDeficit z+primePart z)-H z*(psiDeficit (z-1)+primePart (z-1))-
        k*(F z*(z/exp (z/2)))*GM.error (exp z)+
          (H z*((z-1)/exp ((z-1)/2)))*GM.error (exp (z-1)) := by ring
    _ = _ := by rw [F_error,H_error hz1]; ring

noncomputable def margin (k a b z : ℝ) : ℝ :=
  SharpBase.sharpBase z+k*F z*a-H z*b-(q z)^2*Q z-
    T z*GM.pairBudget k (exp (z-1)) (exp z)

/-- The complete nonlinear arithmetic consumer. The only pair estimate used
below is the already proved signed GM theorem from the original source inputs. -/
theorem actual_margin (hRH : SharedRH.hypothesis) (hGM : GM_Q_Theorem1_1)
    (hP : Buthe.v1.theorem_2_psi) (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hTab : Buthe.v1.table_1_interval_bounds)
    (hL : Buthe.v1.theorem_2_li_minus_pi) (hU : Buthe.v1.theorem_2_li_gt_pi)
    {l u z k a b : ℝ} (hl : 27 ≤ l) (hu : u ≤ 42) (hlz : l ≤ z) (hzu : z ≤ u)
    (hcut : (480000000000:ℝ) ≤ exp z) (hcap : exp z ≤ 640000000000)
    (hk0 : 0 ≤ k) (hke : k ≤ exp 1) (hkw : k ≤ 2*pN 20 u)
    (ha : a ≤ -88/100+lowerPowers l u)
    (hb : 68/100+upperPowers (l-1) ≤ b) : margin k a b z ≤ RamStudy.RG (exp z) := by
  have hz27 : (27:ℝ) ≤ z := hl.trans hlz
  have hz0 : 0 < z := by linarith
  have hzm1 : 0 < z-1 := by linarith
  have hz42 : z ≤ 42 := hzu.trans hu
  have hz2 : 2 ≤ exp z := exp_one_gt_two.le.trans (exp_le_exp.mpr (by linarith))
  have hc0 := (source_deficit_pos hU hz0 hz2 hz42).le
  have hcq := source_deficit_upper hL hz0 hz2 hz42
  have hsq := pow_le_pow_left₀ hc0 hcq 2
  have hF : 0 ≤ F z := by unfold F; positivity
  have hH : 0 ≤ H z := by unfold H; positivity
  have hQ : 0 ≤ Q z := by unfold Q; positivity
  have hT : 0 ≤ T z := by unfold T; positivity
  have hbase := SharpBase.actual_sharp_base hz27
  have hactual := actual_signed_gap (by linarith : 1 < z) hbase
    (le_refl (deficit z)) (le_refl (deficit (z-1)))
  have hactual' : SharpBase.sharpBase z-H z*deficit (z-1)+
      2*RamStudy.w z*F z*deficit z-(deficit z)^2*Q z ≤ RamStudy.RG (exp z) := by
    convert hactual using 1 <;> unfold F H Q <;> ring
  have hw : pN 20 u ≤ RamStudy.w z :=
    (pN_antitone hz0 hzu 20).trans (by
      simpa only [actual_w_eq] using (actual_factorial_barrier26 (by linarith : 26 ≤ z)).1)
  have hkactual : k ≤ 2*RamStudy.w z := by linarith
  have hkwc := mul_le_mul_of_nonneg_right hkactual (mul_nonneg hF hc0)
  have hsqQ := mul_le_mul_of_nonneg_right hsq hQ
  have ht := table1_bridge480 hTab hcut hcap
  have hpow := powers_lower hL (by linarith : 26 ≤ l) hlz hzu hu
  have hpow' := powers_upper hU (by linarith : 26 ≤ l-1)
    (by linarith : l-1 ≤ z-1) (by linarith : z-1 ≤ 42)
  have ha' : a ≤ psiDeficit z+primePart z := by linarith
  have hb' : psiDeficit (z-1)+primePart (z-1) ≤ b := by linarith
  have hpa := mul_le_mul_of_nonneg_left ha' (mul_nonneg hk0 hF)
  have hpb := mul_le_mul_of_nonneg_left hb' hH
  have hpair := GM.actual_pair_upper hRH hGM hP hJ hk0 hke
    (y := exp (z-1)) (x := exp z)
    (exp_le_exp.mpr (by linarith)) (exp_le_exp.mpr (by linarith))
  have hpt := mul_le_mul_of_nonneg_left hpair hT
  have hidentity := linear_identity (k := k) hz0.ne' (by linarith : z ≠ 1)
  unfold margin
  nlinarith only [hactual',hkwc,hsqQ,hpa,hpb,hpt,hidentity]

#print axioms deficit_error
#print axioms linear_identity
#print axioms actual_margin
end RHOcticPush.Correlated
