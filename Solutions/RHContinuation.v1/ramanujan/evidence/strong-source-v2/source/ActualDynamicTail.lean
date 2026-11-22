import ActualDynamicMainterm
import ActualTail
namespace RHContinuation.Ramanujan
open Real IEANTN Set Finset RamanujanPV.AnalyticTransition Ramanujan640
open Ramanujan640.RHTail Ramanujan640.AnalyticBarrier Ramanujan640.Polynomial
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option leancert.trust "kernel"
noncomputable def dynamicBase (l : ℝ) : ℝ :=
  l^4*sourcePolynomial (1/l)-analyticError (1/l)
theorem actual_dynamic_tail_profile (hRH : SharedRH.hypothesis)
    (hButhe : Buthe2016.v1.theorem_2_li_minus_pi)
    {l : ℝ} (hl : 42 ≤ l) : dynamicBase l-D a l ≤ RamStudy.RG (exp l) := by
  have hl0 : 0 < l := by linarith
  have hl1 : 1 < l := by linarith
  have hlm : l-1 ≠ 0 := by linarith
  let B : ℝ := dynamicBase l
  have hbase : B ≤ l^4*(l/(l-1)*RamStudy.w (l-1)-(RamStudy.w l)^2) := by
    simpa only [B,dynamicBase] using actual_dynamic_base (by linarith : (27:ℝ)≤l)
  have hw : RamStudy.w l ≤ 21/20 := by
    have h := actual_w_tail_no_series hl
    simpa only [w_actual_eq] using h
  have hc := actual_count_RH_bounds hRH hButhe (l:=l) (by linarith)
  have hd := actual_count_RH_bounds hRH hButhe (l:=l-1) (by linarith)
  have hs := RamStudy.signed_consumer hl1 hbase
    (show RamStudy.count l ≤ RamStudy.w l-(-eta l) by linarith [hc.2]) hd.1
  have hsign : B-l^4*(l/(l-1)*eta (l-1))-
      l^4*(2*RamStudy.w l*eta l)-l^4*(eta l)^2 ≤ RamStudy.RG (exp l) := by
    convert! hs using 1 <;> ring
  have hshift : l^4*(l/(l-1)*eta (l-1)) =
      a*l^5*(l-1)*exp ((1-l)/2) := by
    unfold eta
    rw [show -(l-1)/2=(1-l)/2 by ring]
    field_simp [hlm]
    <;> ring
  have hetanonneg : 0 ≤ eta l := by unfold eta;exact mul_nonneg (mul_nonneg a_bounds.1 (sq_nonneg _)) (exp_pos _).le
  have hcross : l^4*(2*RamStudy.w l*eta l) ≤
      (21/10:ℝ)*a*l^6*exp (-l/2) := by
    have h := mul_le_mul_of_nonneg_left hw (show 0 ≤ 2*l^4*eta l by positivity)
    dsimp [eta] at h ⊢
    nlinarith
  have hsquare : l^4*(eta l)^2 = a^2*l^8*exp (-l) := by
    have he : exp (-l/2)^2=exp (-l) := by
      rw [← exp_nat_mul]
      congr 1
      ring
    unfold eta
    rw [mul_pow,mul_pow,he]
    ring
  rw [hshift,hsquare] at hsign
  dsimp [B] at hsign
  unfold D
  linarith



noncomputable def powerExp (n : ℕ) (b z : ℝ) : ℝ := z^(n+1)*exp (-b*z)
lemma powerExp_derivative (n : ℕ) (b z : ℝ) :
    HasDerivAt (powerExp n b)
      (z^n*((n+1:ℕ)-b*z)*exp (-b*z)) z := by
  have h := ((hasDerivAt_id z).pow (n+1)).mul
    (((hasDerivAt_id z).const_mul (-b)).exp)
  convert! h using 1 <;> simp [powerExp,pow_succ] <;> ring
lemma powerExp_antitone (n : ℕ) {b : ℝ} (hb : 0 ≤ b)
    (hn : (n+1:ℕ) ≤ b*70) : AntitoneOn (powerExp n b) (Ici (70:ℝ)) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici _)
  · intro z hz;exact (powerExp_derivative n b z).continuousAt.continuousWithinAt
  · intro z hz;exact (powerExp_derivative n b z).differentiableAt.differentiableWithinAt
  · intro z hz
    rw [(powerExp_derivative n b z).deriv]
    have hza : (70:ℝ) ≤ z := interior_subset hz
    have hz0 : 0 ≤ z := by linarith
    have hc : (n+1:ℕ)-b*z ≤ 0 := by nlinarith
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hz0 n) hc) (exp_pos _).le

noncomputable def scaledLossBound (c l : ℝ) : ℝ :=
  (c*exp (1/2)+(21/10:ℝ)*c)*powerExp 7 (1/2) l+c^2*powerExp 9 1 l
lemma D_scaled_bound {c l : ℝ} (hc : 0 ≤ c) (hl : 1 ≤ l) :
    l^2*D c l ≤ scaledLossBound c l := by
  have hl0 : 0 ≤ l := by linarith
  have he : exp ((1-l)/2)=exp (1/2)*exp (-l/2) := by
    rw [← exp_add];congr 1;ring
  have hm := mul_le_mul_of_nonneg_left (show l-1 ≤ l by linarith)
    (show 0 ≤ c*l^7*exp (1/2)*exp (-l/2) by positivity)
  unfold D scaledLossBound powerExp
  rw [he]
  norm_num only [Nat.add_one_sub_one,Nat.reduceAdd,one_mul] at *
  simp only [show -(1/2:ℝ)*l = -l/2 by ring,neg_one_mul]
  nlinarith only [hm]
lemma scaledLossBound_decreases {c l : ℝ} (hc : 0 ≤ c) (hl : 70 ≤ l) :
    scaledLossBound c l ≤ scaledLossBound c 70 := by
  have hp := powerExp_antitone 7 (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
    (show (70:ℝ) ∈ Set.Ici (70:ℝ) by simp) hl hl
  have hq := powerExp_antitone 9 (by norm_num : (0:ℝ) ≤ 1) (by norm_num)
    (show (70:ℝ) ∈ Set.Ici (70:ℝ) by simp) hl hl
  exact add_le_add (mul_le_mul_of_nonneg_left hp (by positivity))
    (mul_le_mul_of_nonneg_left hq (sq_nonneg c))
lemma scaledLossBound_endpoint : scaledLossBound (25/628:ℝ) 70 ≤ 1/2 := by
  unfold scaledLossBound powerExp
  interval_decide 80 (trust := kernel)
lemma actual_D_small {l : ℝ} (hl : 70 ≤ l) : D a l ≤ 1/(2*l^2) := by
  have hl0 : 0 < l := by linarith
  have hc := D_mono_c a_bounds.1 a_bounds.2 (by linarith : (1:ℝ) ≤ l)
  have hmul := mul_le_mul_of_nonneg_left hc (sq_nonneg l)
  have hb := D_scaled_bound (by norm_num : (0:ℝ) ≤ 25/628) (by linarith : (1:ℝ) ≤ l)
  have hm := scaledLossBound_decreases (by norm_num : (0:ℝ) ≤ 25/628) hl
  have H : l^2*D a l ≤ (1/2:ℝ) := hmul.trans (hb.trans (hm.trans scaledLossBound_endpoint))
  apply (le_div_iff₀ (show 0 < 2*l^2 by positivity)).2
  nlinarith
lemma dynamicBase_lower {l : ℝ} (hl : 0 < l) :
    1+14/l+145/l^2+1412/l^3-analyticError (1/l) ≤ dynamicBase l := by
  have h := mul_le_mul_of_nonneg_left (difference_lower (1/l) (by positivity))
    (show 0 ≤ l^4 by positivity)
  unfold dynamicBase
  rw [sourcePolynomial_eq]
  have hh : 1+14/l+145/l^2+1412/l^3 ≤ l^4*difference (1/l) := by
    convert! h using 1 <;> field_simp <;> ring
  linarith
/-- A nonconstant actual-RG lower profile tending to1, with all li analytic
identities and variable factorial-square remainder proved, not assumed. -/
theorem actual_tail_144 (hRH : SharedRH.hypothesis)
    (hS : Buthe2016.v1.theorem_2_li_minus_pi)
    {l : ℝ} (hl : 70 ≤ l) :
    1+14/l+144/l^2 ≤ RamStudy.RG (exp l) := by
  have h := actual_dynamic_tail_profile hRH hS (by linarith : (42:ℝ) ≤ l)
  have hB := dynamicBase_lower (by linarith : (0:ℝ) < l)
  have hE := analyticError_small (by linarith : (60:ℝ) ≤ l)
  have hD := actual_D_small hl
  have hp : 0 ≤ 1412/l^3 := by positivity
  have he : 1/(2*l^2)+1/(2*l^2)=1/l^2 := by ring
  have he145 : 145/l^2-1/l^2=144/l^2 := by ring
  linarith
#print axioms actual_dynamic_tail_profile
#print axioms actual_tail_144
end RHContinuation.Ramanujan
