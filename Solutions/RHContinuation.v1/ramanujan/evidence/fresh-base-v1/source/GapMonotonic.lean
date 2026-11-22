import LeafMargins
import ActualConsumer
namespace Ramanujan640
open Real Set
set_option maxHeartbeats 0
set_option maxRecDepth 100000

noncomputable def baseBound (z : ℝ) : ℝ :=
  1+14/z+145/z^2+1412/z^3-1/1000
noncomputable def weight (b z : ℝ) : ℝ := z^4*exp (-b*z)
noncomputable def shiftWeight (z : ℝ) : ℝ := z^5/(z-1)*exp ((1-z)/2)

theorem weight_derivative (b z : ℝ) :
    HasDerivAt (weight b) (z^3*(4-b*z)*exp (-b*z)) z := by
  have h := ((hasDerivAt_id z).pow 4).mul
    (((hasDerivAt_id z).const_mul (-b)).exp)
  convert! h using 1 <;> simp [weight] <;> ring

theorem weight_antitone {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 4 ≤ b*a) :
    AntitoneOn (weight b) (Ici a) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici _)
  · intro z hz;exact (weight_derivative b z).continuousAt.continuousWithinAt
  · intro z hz;exact (weight_derivative b z).differentiableAt.differentiableWithinAt
  · intro z hz
    rw [(weight_derivative b z).deriv]
    have hza : a ≤ z := interior_subset hz
    have hz0 : 0 ≤ z := ha.trans hza
    have hc : 4-b*z ≤ 0 := by nlinarith
    exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hz0 _) hc)
      (exp_pos _).le

theorem shift_derivative {z : ℝ} (hz : 1 < z) :
    HasDerivAt shiftWeight
      (shiftWeight z*(5/z-1/(z-1)-1/2)) z := by
  have hd := (((hasDerivAt_id z).pow 5).div ((hasDerivAt_id z).sub_const 1)
    (show z-1 ≠ 0 by linarith)).mul
    (((hasDerivAt_const z (1:ℝ)).sub (hasDerivAt_id z)).div_const 2).exp
  convert! hd using 1
  dsimp [shiftWeight]
  field_simp [show z ≠ 0 by linarith,show z-1 ≠ 0 by linarith]
  <;> ring

theorem shift_antitone : AntitoneOn shiftWeight (Ici (27:ℝ)) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici _)
  · intro z hz
    have hz27 : (27:ℝ) ≤ z := hz
    exact (shift_derivative (show 1 < z by linarith)).continuousAt.continuousWithinAt
  · intro z hz
    have hz27 : (27:ℝ) ≤ z := interior_subset hz
    exact (shift_derivative (show 1 < z by linarith)).differentiableAt.differentiableWithinAt
  · intro z hz
    have hz27 : (27:ℝ) ≤ z := interior_subset hz
    rw [(shift_derivative (show 1 < z by linarith)).deriv]
    have hq : 1/z ≤ (1/27:ℝ) := one_div_le_one_div_of_le (by norm_num) hz27
    have hz0 : 0 < z := by linarith
    have hzm : 0 < z-1 := by linarith
    have hi : 0 ≤ 1/(z-1) := by positivity
    have hq5 : 5/z ≤ (5/27:ℝ) := by
      simpa only [div_eq_mul_inv,one_mul,mul_assoc] using
        mul_le_mul_of_nonneg_left hq (by norm_num : (0:ℝ)≤5)
    have hc : 5/z-1/(z-1)-1/2 ≤ 0 := by linarith [hq5]
    have hp : 0 ≤ shiftWeight z := by unfold shiftWeight;positivity
    exact mul_nonpos_of_nonneg_of_nonpos hp hc

theorem base_antitone {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    baseBound b ≤ baseBound a := by
  have h1 := one_div_le_one_div_of_le ha hab
  have h2 := one_div_le_one_div_of_le (pow_pos ha 2) (pow_le_pow_left₀ ha.le hab 2)
  have h3 := one_div_le_one_div_of_le (pow_pos ha 3) (pow_le_pow_left₀ ha.le hab 3)
  unfold baseBound
  simp only [div_eq_mul_inv] at *
  linarith

/-- Endpoint arithmetic is consumed by the actual-G theorem, using proved
monotonic weights rather than a sampled monotonicity assertion. -/
theorem actual_slab_consumer {l u z c d : ℝ} (hl : 27 ≤ l)
    (hlz : l ≤ z) (hzu : z ≤ u) (hc0 : 0 ≤ c) (hd0 : 0 ≤ d)
    (hbase : baseBound z ≤ z^4*(z/(z-1)*RamStudy.w (z-1)-(RamStudy.w z)^2))
    (hwl : 1+1/z ≤ RamStudy.w z)
    (hc : c ≤ deficit z) (hd : deficit (z-1) ≤ d) :
    endpointMargin l u c d ≤ RamStudy.RG (exp z) := by
  have hz27 : (27:ℝ) ≤ z := hl.trans hlz
  have hu27 : (27:ℝ) ≤ u := hz27.trans hzu
  have h := actual_signed_gap (show 1 < z by linarith) hbase hc hd
  have hB := base_antitone (show 0 < z by linarith) hzu
  have hwF := weight_antitone (a:=l) (b:=(1/2:ℝ)) (by linarith) (by norm_num) (by linarith)
  have hF1 := hwF hlz (hlz.trans hzu) hzu
  have hF := mul_le_mul_of_nonneg_left hF1 hc0
  have hwQ := weight_antitone (a:=l) (b:=(1:ℝ)) (by linarith) (by norm_num) (by linarith)
  have hQ1 := hwQ (show l ∈ Ici l by simp) hlz hlz
  have hQ := mul_le_mul_of_nonneg_left hQ1 (sq_nonneg c)
  have hH := mul_le_mul_of_nonneg_left (shift_antitone hl hz27 hlz) hd0
  have hwi : 1/u ≤ 1/z := one_div_le_one_div_of_le (by linarith) hzu
  have hw : 1+1/u ≤ RamStudy.w z := by linarith
  have hF0 : 0 ≤ c*weight (1/2) u := by unfold weight;positivity
  have hw0 : 0 ≤ RamStudy.w z := by
    have hzp : 0 < z := by linarith
    have hrec : 0 < 1/z := by positivity
    linarith
  have hprod := mul_le_mul hw hF hF0 hw0
  unfold endpointMargin baseBound weight shiftWeight at *
  norm_num only [one_mul, neg_one_mul] at *
  have hnz : -(1/2:ℝ)*z = -z/2 := by ring
  have hnu : -(1/2:ℝ)*u = -u/2 := by ring
  simp only [hnz,hnu] at *
  simp only [div_eq_mul_inv] at h hB hH hQ hprod ⊢
  nlinarith only [h,hB,hH,hQ,hprod]

#print axioms weight_antitone
#print axioms shift_antitone
#print axioms actual_slab_consumer
end Ramanujan640
