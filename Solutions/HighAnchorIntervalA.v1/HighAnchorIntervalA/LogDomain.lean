/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import HighAnchorIntervalA.Common
import DirectIntervalA.LogDomain

namespace HighAnchorIntervalA
open Real Set MeasureTheory
set_option maxHeartbeats 0

theorem gap_pos (L : ℝ) : 0<gap L := by unfold gap c;positivity
theorem delta_pos (L : ℝ) : 0<delta L := by unfold delta c;positivity
theorem truncHeight_pos {L : ℝ} (hL : 330≤L) : 0<truncHeight L := by
  unfold truncHeight
  have hL0 : 0<L := by linarith
  positivity

theorem delta_le_hundredth {L : ℝ} (hL : 330≤L) : delta L≤1/100 := by
  have he : exp (-eta*L)≤exp (-L/5) := exp_le_exp.mpr (by dsimp [eta];linarith)
  have hc : c≤1 := by norm_num [c]
  calc
    _ ≤ 1*exp (-L/5) := mul_le_mul hc he (exp_pos _).le (by norm_num)
    _ ≤ _ := by simpa only [one_mul,DirectIntervalA.delta] using DirectIntervalA.delta_le_hundredth hL

theorem delta_le_one {L : ℝ} (hL : 330≤L) : delta L≤1 :=
  (delta_le_hundredth hL).trans (by norm_num)

theorem two_add_delta_le_cap {L : ℝ} (hL : 330≤L) : 2+delta L≤201/100 := by
  linarith [delta_le_hundredth hL]

theorem delta_mul_U (L : ℝ) : delta L*U L=(201/100:ℝ) := by
  unfold delta U
  calc
    _ = c*k*(exp (-eta*L)*exp (eta*L)) := by ring
    _ = _ := by rw [←exp_add];norm_num [c,k]

theorem gap_ratio (L : ℝ) : gap L/exp L=delta L := by
  unfold gap delta
  rw [mul_div_assoc,←exp_sub]
  congr 1
  norm_num [alpha,eta]
  ring

theorem gap_mul_U (L : ℝ) : gap L*U L=(201/100:ℝ)*exp L := by
  unfold gap U
  calc
    _ = (c*k)*(exp (alpha*L)*exp (eta*L)) := by ring
    _ = _ := by rw [←exp_add];norm_num [c,k,alpha,eta];congr 1;ring

theorem exp_29_large : (3*(10:ℝ)^12)≤exp 29 := by
  have hb : (27/10:ℝ)≤exp 1 := by linarith [Real.exp_one_gt_d9]
  calc
    _ ≤ (27/10:ℝ)^29 := by norm_num
    _ ≤ (exp 1)^29 := by gcongr
    _ = _ := by rw [←Real.exp_nat_mul];norm_num

theorem U_ge_profileHeight {L : ℝ} (hL : 330≤L) : profileHeight≤U L := by
  have hh:=mul_le_mul_of_nonneg_right exp_29_large (exp_pos (40:ℝ)).le
  rw [←exp_add] at hh
  have he : exp (29+40:ℝ)≤exp (eta*L) := exp_le_exp.mpr (by dsimp [eta];linarith)
  have hp:=exp_pos (eta*L)
  unfold profileHeight U
  have hk : (1:ℝ)≤k := by norm_num [k]
  nlinarith

theorem U_ge_height {L : ℝ} (hL : 330≤L) : 3*(10:ℝ)^12≤U L := by
  have hh:=U_ge_profileHeight hL
  have he : (1:ℝ)≤exp 40 := one_le_exp (by norm_num)
  unfold profileHeight at hh
  nlinarith

theorem U_le_V {L : ℝ} (hL : 330≤L) : U L≤V L := by
  have he:=exp_pos (eta*L)
  unfold U V truncHeight
  have hc : k≤2*(3000/23:ℝ)*L := by norm_num [k];linarith
  nlinarith

theorem truncHeight_lower {L : ℝ} (hL : 330≤L) : max 51 (L^2)<truncHeight L := by
  have he:=add_one_le_exp (eta*L)
  have hm:=mul_le_mul_of_nonneg_left he (show 0≤(3000/23:ℝ)*L by linarith)
  unfold truncHeight
  dsimp [eta] at hm
  apply max_lt_iff.mpr
  constructor <;> nlinarith [sq_nonneg L]

theorem exp_large {L : ℝ} (hL : 330≤L) : 7000*(L+1)≤exp ((29/100:ℝ)*L) := by
  have hc : (330:ℝ)^3≤L^3 := by gcongr
  have hq:=mul_le_mul_of_nonneg_right hc (show 0≤L by linarith)
  have he:=pow_div_factorial_le_exp ((29/100:ℝ)*L) (show 0≤(29/100:ℝ)*L by linarith) 4
  norm_num at hc hq he
  nlinarith

theorem truncHeight_upper {L : ℝ} (hL : 330≤L) :
    truncHeight L<(sqrt (exp L)-2)/4 := by
  have he:=exp_pos (eta*L)
  have he1 : (1:ℝ)≤exp (eta*L) := one_le_exp (by dsimp [eta];linarith)
  have hb : 4*(3000/23:ℝ)*L+2<exp ((29/100:ℝ)*L) := by linarith [exp_large hL]
  have hm:=mul_lt_mul_of_pos_right hb he
  have hmul : exp ((29/100:ℝ)*L)*exp (eta*L)=exp (L/2) := by
    rw [←exp_add];congr 1;dsimp [eta];ring
  rw [hmul] at hm
  rw [←Real.exp_half]
  unfold truncHeight
  nlinarith

theorem truncation_domain {L : ℝ} (hL : 330≤L) :
    max 51 (log (exp L)^2)<truncHeight L ∧ truncHeight L<(sqrt (exp L)-2)/4 := by
  rw [log_exp]
  exact ⟨truncHeight_lower hL,truncHeight_upper hL⟩

theorem gap_le_exp {L : ℝ} (hL : 330≤L) : gap L≤exp L := by
  have he : exp (alpha*L)≤exp L := exp_le_exp.mpr (by dsimp [alpha];linarith)
  unfold gap
  exact (mul_le_mul_of_nonneg_left he (by norm_num [c])).trans
    (by have hh:=exp_pos L;norm_num [c];linarith)

end HighAnchorIntervalA
#print axioms HighAnchorIntervalA.U_ge_profileHeight
#print axioms HighAnchorIntervalA.truncation_domain
