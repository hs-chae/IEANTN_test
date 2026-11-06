/- Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import E1NPlus.LogDomain
import E1NPlus.Bands
namespace E1NPlus
open Real Set
set_option maxHeartbeats 0
noncomputable def vlog (L:ℝ):ℝ:=eta*L+log ((1200000/43:ℝ)*L)
noncomputable def wlog (L:ℝ):ℝ:=vlog L-ulog L

theorem log_V {L:ℝ} (hL:0<L) : log (V L)=vlog L := by
  have he:V L=((1200000/43:ℝ)*L)*exp (eta*L) := by unfold V truncHeight;ring
  rw [he,log_mul (by positivity) (exp_pos _).ne',log_exp]
  unfold vlog
  ring

theorem log_scale_bound {A L:ℝ} (hA:0<A) (hL:330 ≤ L)
    (ha:1 ≤ log (A*330)) : log (A*L) ≤ log (A*330)*(L/330) := by
  have hL0:0<L:=by linarith
  have hr:1 ≤ L/330:=by linarith
  have hid:A*L=(A*330)*(L/330) := by ring
  rw [hid,log_mul (by positivity) (by positivity)]
  have hl:=log_le_sub_one_of_pos (show 0<L/330 by positivity)
  have hm:=mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hr)
  nlinarith

theorem wlog_eq {L:ℝ} (hL:0<L) : wlog L=log (((1200000/43:ℝ)/k)*L) := by
  have hid:((1200000/43:ℝ)/k)*L=((1200000/43:ℝ)*L)/k := by ring
  rw [hid,log_div (by positivity) (by norm_num [k] : k≠0)]
  unfold wlog vlog ulog
  ring

theorem v330_upper : vlog 330 ≤ (427/5:ℝ) := by
  have hh:=log_v_coefficient_upper
  norm_num [vlog,eta] at hh ⊢
  linarith

theorem w330_bounds : (1:ℝ) ≤ wlog 330 ∧ wlog 330 ≤ 77/5 := by
  constructor
  · rw [wlog_eq (by norm_num : (0:ℝ)<330)]
    have he:exp (1:ℝ) ≤ ((1200000/43:ℝ)/k)*330 := by
      have hx:=exp_one_lt_d9
      norm_num [k] at ⊢
      linarith
    simpa only [log_exp] using log_le_log (exp_pos (1:ℝ)) he
  · unfold wlog
    linarith [v330_upper,u330_bounds.1]

theorem u_scale {L:ℝ} (hL:330 ≤ L) : ulog L ≤ (1403/20:ℝ)*(L/330) := by
  have hr:1 ≤ L/330:=by linarith
  have hk0:0 ≤ log k:=by linarith [log_k_bounds.1]
  have hm:=mul_nonneg hk0 (sub_nonneg.mpr hr)
  have hu:=mul_le_mul_of_nonneg_right u330_bounds.2 (show 0 ≤ L/330 by linarith)
  unfold ulog eta at hu ⊢
  nlinarith

theorem v_scale {L:ℝ} (hL:330 ≤ L) : vlog L ≤ (427/5:ℝ)*(L/330) := by
  have ha:1 ≤ log ((1200000/43:ℝ)*330) := by
    have he:exp (1:ℝ) ≤ (1200000/43:ℝ)*330 := by linarith [exp_one_lt_d9]
    simpa only [log_exp] using log_le_log (exp_pos (1:ℝ)) he
  have hs:=log_scale_bound (by norm_num : (0:ℝ)<1200000/43) hL ha
  have hu:=mul_le_mul_of_nonneg_right v330_upper (show 0 ≤ L/330 by linarith)
  unfold vlog eta at hu ⊢
  nlinarith

theorem w_scale {L:ℝ} (hL:330 ≤ L) :
    (1:ℝ) ≤ wlog L ∧ wlog L ≤ (77/5:ℝ)*(L/330) := by
  have hL0:0<L:=by linarith
  have hA:0<(1200000/43:ℝ)/k:=by norm_num [k]
  have he1:1 ≤ log (((1200000/43:ℝ)/k)*330) := by
    simpa only [←wlog_eq (by norm_num : (0:ℝ)<330)] using w330_bounds.1
  have hs:=log_scale_bound hA hL he1
  have hl:=log_le_log (show 0<((1200000/43:ℝ)/k)*330 by positivity)
    (mul_le_mul_of_nonneg_left hL hA.le)
  rw [←wlog_eq hL0,←wlog_eq (by norm_num : (0:ℝ)<330)] at hs hl
  constructor
  · exact w330_bounds.1.trans hl
  · exact hs.trans (mul_le_mul_of_nonneg_right w330_bounds.2 (show 0 ≤ L/330 by linarith))

theorem low_shape_bound {L:ℝ} (hL:330 ≤ L) :
    vlog L+(vlog L^2-ulog L^2)/2 ≤ (12843/10:ℝ)*(L/330)^2 := by
  have hr:1 ≤ L/330:=by linarith
  have hr0:0 ≤ L/330:=by linarith
  have hrr:L/330 ≤ (L/330)^2:=by nlinarith [mul_nonneg hr0 (sub_nonneg.mpr hr)]
  have hu:=u_scale hL
  have hv:=v_scale hL
  have hw:=w_scale hL
  have hw0:0 ≤ wlog L:=by linarith [hw.1]
  have huw:=mul_le_mul hu hw.2 hw0 (show 0 ≤ (1403/20:ℝ)*(L/330) by positivity)
  have hww:=pow_le_pow_left₀ hw0 hw.2 2
  have hvv:=mul_le_mul_of_nonneg_left hrr (show (0:ℝ) ≤ 427/5 by norm_num)
  have hid:vlog L+(vlog L^2-ulog L^2)/2=vlog L+ulog L*wlog L+wlog L^2/2 := by
    unfold wlog
    ring
  rw [hid]
  nlinarith

theorem quadratic_exp_antitone :
    AntitoneOn (fun L:ℝ↦L^2*exp (-L/25)) (Ici 330) := by
  let d:ℝ→ℝ:=fun L↦exp (-L/25)*(2*L-L^2/25)
  have hd:∀L:ℝ,HasDerivAt (fun t:ℝ↦t^2*exp (-t/25)) (d L) L := by
    intro L
    have hh:=((hasDerivAt_id L).pow 2).mul ((((hasDerivAt_id L).neg).div_const (25:ℝ)).exp)
    convert! hh using 1 <;> dsimp [d] <;> ring
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici (330:ℝ))
    (fun L _↦(hd L).continuousAt.continuousWithinAt)
    (fun L _↦(hd L).hasDerivWithinAt)
  intro L hL
  have hLL:(330:ℝ) ≤ L:=interior_subset hL
  unfold d
  apply mul_nonpos_of_nonneg_of_nonpos (exp_pos _).le
  nlinarith [mul_nonneg (show 0 ≤ L by linarith) (show 0 ≤ L-50 by linarith)]

theorem scaled_exp_bound {L:ℝ} (hL:330 ≤ L) :
    exp (-L/25)*(L/330)^2 ≤ (1/530000:ℝ) := by
  have hh:=quadratic_exp_antitone (by simp : (330:ℝ)∈Ici 330) hL hL
  norm_num at hh
  have he:exp (-(66/5:ℝ)) ≤ (1/530000:ℝ) := by
    rw [exp_neg,←one_div]
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) exp13_2_lower
  have hp:exp (-L/25)*(L/330)^2 ≤ exp (-(66/5:ℝ)) := by nlinarith
  exact hp.trans he

theorem low_le {L:ℝ} (hL:330 ≤ L) : low L ≤ (19/10000:ℝ) := by
  have hL0:0<L:=by linarith
  have hk0:0 ≤ k/Real.pi:=by unfold k;positivity
  have hk:k/Real.pi ≤ (39/50:ℝ) := by
    apply (div_le_iff₀ pi_pos).mpr
    norm_num [k] at ⊢
    linarith [Real.pi_gt_three]
  have hs:=low_shape_bound hL
  unfold low
  rw [log_V hL0]
  calc
    _ ≤ (k/Real.pi)*exp (-L/25)*((12843/10:ℝ)*(L/330)^2) :=
      mul_le_mul_of_nonneg_left hs (mul_nonneg hk0 (exp_pos _).le)
    _ = (k/Real.pi)*(12843/10)*(exp (-L/25)*(L/330)^2) := by ring
    _ ≤ (39/50:ℝ)*(12843/10)*(1/530000) := by
      gcongr
      exact scaled_exp_bound hL
    _ ≤ _ := by norm_num
#print axioms low_le
end E1NPlus
