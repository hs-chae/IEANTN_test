/- Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import E1NPlus.HighEndpoint
namespace E1NPlus
open Real Set MeasureTheory
set_option maxHeartbeats 0

theorem main330_continuous : ContinuousOn (fun s:ℝ↦mainRay s 330) (Icc (3/4:ℝ) (7/8:ℝ)) := by
  intro s hs
  have hu:0<ulog 330:=by linarith [u330_bounds.1]
  have hb0:0<b s:=by dsimp [b,p];linarith [hs.1]
  have hb:b s≠0:=hb0.ne'
  have hbu:b s*ulog 330≠0:=mul_ne_zero hb hu.ne'
  unfold mainRay coeff rate E1FrozenN.Interval.factor4
  dsimp only [E1FrozenN.Interval.q,E1FrozenN.Interval.b,E1FrozenN.Interval.p,b,p,q] at hb hbu ⊢
  fun_prop (disch:=first | assumption | positivity)

theorem main330_integrable {l r:ℝ} (hl:(3/4:ℝ) ≤ l) (hr:r ≤ 7/8) (hlr:l ≤ r) :
    IntervalIntegrable (fun s:ℝ↦mainRay s 330) volume l r := by
  apply ContinuousOn.intervalIntegrable
  refine main330_continuous.mono ?_
  intro s hs
  rw [uIcc_of_le hlr] at hs
  exact ⟨by linarith [hs.1],by linarith [hs.2]⟩

theorem exp_band_integral {a l r:ℝ} (ha:a≠0) :
    (∫s in l..r,exp (-a*bandDelta s))=
      (exp (-a*bandDelta r)-exp (-a*bandDelta l))/a := by
  have hd:∀t∈uIcc l r,HasDerivAt
      (fun s:ℝ↦exp (-a*bandDelta s)/a) (exp (-a*bandDelta t)) t := by
    intro t _
    have hh:=((((hasDerivAt_const t (7/8:ℝ)).sub (hasDerivAt_id t)).const_mul (-a)).exp).div_const a
    convert! hh using 1 <;> dsimp [bandDelta] <;> field_simp [ha] <;> ring
  have hi:IntervalIntegrable (fun s:ℝ↦exp (-a*bandDelta s)) volume l r := by
    apply Continuous.intervalIntegrable
    unfold bandDelta
    fun_prop
  have he:=intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  convert he using 1 <;> ring

theorem main330_integral_band {l r a G:ℝ} (hl:(3/4:ℝ) ≤ l) (hr:r ≤ 7/8) (hlr:l ≤ r)
    (ha:a≠0) (hbound:∀s∈Icc l r,mainRay s 330 ≤ mainPref*G*exp (-a*bandDelta s)) :
    (∫s in l..r,mainRay s 330) ≤
      (mainPref*G)*((exp (-a*bandDelta r)-exp (-a*bandDelta l))/a) := by
  have hi:=main330_integrable hl hr hlr
  have hb:IntervalIntegrable (fun s:ℝ↦mainPref*G*exp (-a*bandDelta s)) volume l r := by
    apply Continuous.intervalIntegrable
    unfold bandDelta
    fun_prop
  calc
    _ ≤ ∫s in l..r,mainPref*G*exp (-a*bandDelta s) :=
      intervalIntegral.integral_mono_on hlr hi hb hbound
    _ = _ := by rw [intervalIntegral.integral_const_mul,exp_band_integral ha]

theorem main330_integral_near :
    (∫s in (69/80:ℝ)..(7/8:ℝ),mainRay s 330) ≤ mainPref*nearG*((817/1000)/a1) := by
  have hh:=main330_integral_band (l:=(69/80:ℝ)) (r:=(7/8:ℝ)) (a:=a1) (G:=nearG)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [a1]) (fun _ hs↦main330_near hs)
  have h0:bandDelta (7/8)=0:=by norm_num [bandDelta]
  have h1:-a1*bandDelta (69/80)=-(a1/80):=by unfold bandDelta;ring
  rw [h0,mul_zero,exp_zero,h1] at hh
  have hg:0 ≤ mainPref*nearG:=by norm_num [mainPref,K,nearG,g4]
  have he:(1-exp (-(a1/80)))/a1 ≤ (817/1000)/a1 := by
    apply div_le_div_of_nonneg_right _ (by norm_num [a1] : 0 ≤ a1)
    linarith [exp_neg_a1_lower]
  exact hh.trans (mul_le_mul_of_nonneg_left he hg)

theorem main330_integral_mid :
    (∫s in (17/20:ℝ)..(69/80:ℝ),mainRay s 330) ≤ mainPref*midG*((1513/10000)/a2) := by
  have hh:=main330_integral_band (l:=(17/20:ℝ)) (r:=(69/80:ℝ)) (a:=a2) (G:=midG)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [a2]) (fun _ hs↦main330_mid hs)
  have h0:-a2*bandDelta (69/80)=-(a2/80):=by unfold bandDelta;ring
  have h1:-a2*bandDelta (17/20)=-(a2/40):=by unfold bandDelta;ring
  rw [h0,h1] at hh
  have hg:0 ≤ mainPref*midG:=by norm_num [mainPref,K,midG,g4]
  have he:(exp (-(a2/80))-exp (-(a2/40)))/a2 ≤ (1513/10000)/a2 := by
    apply div_le_div_of_nonneg_right _ (by norm_num [a2] : 0 ≤ a2)
    linarith [exp_neg_a2_upper,exp_neg_a2_double_lower]
  exact hh.trans (mul_le_mul_of_nonneg_left he hg)

theorem main330_integral_far :
    (∫s in (3/4:ℝ)..(17/20:ℝ),mainRay s 330) ≤ mainPref*farG*((373/10000)/a3) := by
  have hh:=main330_integral_band (l:=(3/4:ℝ)) (r:=(17/20:ℝ)) (a:=a3) (G:=farG)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [a3]) (fun _ hs↦main330_far hs)
  have h0:-a3*bandDelta (17/20)=-(a3/40):=by unfold bandDelta;ring
  have h1:-a3*bandDelta (3/4)=-(a3/8):=by unfold bandDelta;ring
  rw [h0,h1] at hh
  have hg:0 ≤ mainPref*farG:=by norm_num [mainPref,K,farG,g4]
  have he:(exp (-(a3/40))-exp (-(a3/8)))/a3 ≤ (373/10000)/a3 := by
    apply div_le_div_of_nonneg_right _ (by norm_num [a3] : 0 ≤ a3)
    linarith [exp_neg_a3_upper,exp_pos (-(a3/8))]
  exact hh.trans (mul_le_mul_of_nonneg_left he hg)

theorem main330_integral_upper :
    (∫s in (3/4:ℝ)..(7/8:ℝ),mainRay s 330)<9962/10000 := by
  have h1:=intervalIntegral.integral_add_adjacent_intervals
    (main330_integrable (l:=(3/4:ℝ)) (r:=(17/20:ℝ)) (by norm_num) (by norm_num) (by norm_num))
    (main330_integrable (l:=(17/20:ℝ)) (r:=(69/80:ℝ)) (by norm_num) (by norm_num) (by norm_num))
  have h2:=intervalIntegral.integral_add_adjacent_intervals
    (main330_integrable (l:=(3/4:ℝ)) (r:=(69/80:ℝ)) (by norm_num) (by norm_num) (by norm_num))
    (main330_integrable (l:=(69/80:ℝ)) (r:=(7/8:ℝ)) (by norm_num) (by norm_num) (by norm_num))
  rw [←h2,←h1]
  calc
    _ ≤ mainPref*farG*((373/10000)/a3)+mainPref*midG*((1513/10000)/a2)+mainPref*nearG*((817/1000)/a1) :=
      add_le_add (add_le_add main330_integral_far main330_integral_mid) main330_integral_near
    _ = mainPref*(nearG*((817/1000)/a1)+midG*((1513/10000)/a2)+farG*((373/10000)/a3)) := by ring
    _ < _ := main_three_case_tight
#print axioms main330_integral_upper
end E1NPlus
