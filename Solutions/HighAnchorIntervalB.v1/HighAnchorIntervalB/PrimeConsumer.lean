/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import HighAnchorIntervalB.LogDomain
import DirectIntervalA.PrimeConsumer

namespace HighAnchorIntervalB
open Real Set MeasureTheory
set_option maxHeartbeats 0

theorem endpoint_upper {L : ℝ} (hL : 330≤L) : exp L+gap L≤exp (L+1) := by
  rw [exp_add]
  have hh:=gap_le_exp hL
  have he:=exp_one_gt_two
  nlinarith [exp_pos L]

theorem endpoint_log_upper {L : ℝ} (hL : 330≤L) : log (exp L+gap L)≤L+1 := by
  have hh:=log_le_log (show 0<exp L+gap L by linarith [exp_pos L,gap_pos L]) (endpoint_upper hL)
  simpa only [log_exp] using hh

theorem gap_mul_truncHeight (L : ℝ) : gap L*truncHeight L=240*L*exp L := by
  unfold gap truncHeight
  calc
    _ = (c*(3000/11:ℝ))*L*(exp (alpha*L)*exp (eta*L)) := by ring
    _ = _ := by
      rw [←exp_add,show alpha*L+eta*L=L by dsimp [alpha,eta];ring]
      norm_num [c]

theorem truncation_error_bound {L : ℝ} (hL : 330≤L) :
    (2894/1000:ℝ)*((exp L+gap L)*log (exp L+gap L)+exp L*L)/truncHeight L≤
      (49/2000:ℝ)*gap L := by
  have hT:=truncHeight_pos hL
  have hratio:gap L≤(1/100:ℝ)*exp L:=by
    have hd:=delta_le_hundredth hL
    rw [←gap_ratio L] at hd
    exact (div_le_iff₀ (exp_pos L)).mp hd
  have hy:exp L+gap L≤(101/100:ℝ)*exp L:=by linarith
  have hl:=endpoint_log_upper hL
  have hl0:0≤log (exp L+gap L):=by
    apply log_nonneg
    linarith [Real.add_one_le_exp L,gap_pos L]
  have hnum:(2894/1000:ℝ)*((exp L+gap L)*log (exp L+gap L)+exp L*L)≤
      (2894/1000:ℝ)*((101/100:ℝ)*exp L*(L+1)+exp L*L):=by
    gcongr
  have hcoef:(2894/1000:ℝ)*((201/100:ℝ)*L+101/100)≤(49/2000:ℝ)*240*L:=by nlinarith
  have hs:=mul_le_mul_of_nonneg_left hcoef (exp_pos L).le
  apply (div_le_iff₀ hT).mpr
  apply hnum.trans
  rw [mul_assoc (49/2000:ℝ),gap_mul_truncHeight]
  nlinarith only [hs]

theorem prime_power_error_bound {L : ℝ} (hL : 330≤L) :
    Chebyshev.psi (exp L+gap L)-Chebyshev.theta (exp L+gap L)≤(1/1000:ℝ)*gap L := by
  have hy1:1≤exp L+gap L:=by linarith [Real.add_one_le_exp L,gap_pos L]
  have hpp:=Chebyshev.psi_sub_theta_le hy1
  have hl:=endpoint_log_upper hL
  have hl0:0≤log (exp L+gap L):=log_nonneg hy1
  have hsqrt:=sqrt_le_sqrt (endpoint_upper hL)
  rw [←Real.exp_half] at hsqrt
  have hhalf:exp (1/2:ℝ)≤3:=(exp_le_exp.mpr (by norm_num : (1/2:ℝ)≤1)).trans exp_one_lt_three.le
  have hehalf:exp ((L+1)/2)≤3*exp (L/2):=by
    rw [show (L+1)/2=L/2+1/2 by ring,exp_add]
    exact (mul_le_mul_of_nonneg_left hhalf (exp_pos _).le).trans_eq (by ring)
  have hbound:2*sqrt (exp L+gap L)*log (exp L+gap L)≤6*exp (L/2)*(L+1):=by
    have hs:sqrt (exp L+gap L)≤3*exp (L/2):=hsqrt.trans hehalf
    calc
      _ ≤ 2*(3*exp (L/2))*(L+1) := by gcongr
      _ = _ := by ring
  have hb:=mul_le_mul_of_nonneg_left (exp_large hL) (exp_pos (L/2)).le
  have he:exp (L/2)*exp ((29/100:ℝ)*L)=exp (alpha*L):=by
    rw [←exp_add];congr 1;dsimp [alpha];ring
  rw [he] at hb
  apply hpp.trans
  apply hbound.trans
  unfold gap c
  nlinarith only [hb,exp_pos (alpha*L)]

theorem hasPrime_exp_of_psi_error {L E : ℝ} (hL : 330≤L)
    (herror:|Chebyshev.psi (exp L+gap L)-Chebyshev.psi (exp L)-gap L|≤E*gap L)
    (hmargin:E+1/1000<1) : IEANTN.HasPrimeInInterval (exp L) (gap L) := by
  apply DirectIntervalA.hasPrime_of_psi_increment (E:=E) (P:=1/1000)
    (by linarith [Real.add_one_le_exp L]) (gap_pos L) _ (prime_power_error_bound hL) hmargin
  have hd:=(abs_le.mp herror).1
  linarith

theorem gap_eq_rpow (L : ℝ) : gap L=c*(exp L)^alpha := by
  unfold gap
  rw [Real.rpow_def_of_pos (exp_pos L),log_exp]
  congr 1
  ring

theorem real_ray_of_log_ray
    (h:∀L:ℝ,330≤L→IEANTN.HasPrimeInInterval (exp L) (gap L)) :
    ∀x:ℝ,exp 330≤x→IEANTN.HasPrimeInInterval x (c*x^alpha) := by
  intro x hx
  have hx0:0<x:=(exp_pos 330).trans_le hx
  have hl:330≤log x:=by simpa only [log_exp] using log_le_log (exp_pos (330:ℝ)) hx
  have hp:=h (log x) hl
  rw [gap_eq_rpow,exp_log hx0] at hp
  exact hp

/-- Strict comparison of the actual interval widths; no source-package or
global-winner comparison is hidden in this elementary scalar theorem. -/
theorem interval_width_strict {x : ℝ} (hx:exp 330≤x) :
    (22/25:ℝ)*x^(79/100:ℝ)<x^(4/5:ℝ) := by
  have hx1:1<x:=(one_lt_exp_iff.mpr (by norm_num : (0:ℝ)<330)).trans_le hx
  have hp:=Real.rpow_pos_of_pos (by linarith : 0<x) (79/100:ℝ)
  calc
    _ < x^(79/100:ℝ) := by nlinarith
    _ < _ := Real.rpow_lt_rpow_of_exponent_lt hx1 (by norm_num)

end HighAnchorIntervalB
#print axioms HighAnchorIntervalB.truncation_error_bound
#print axioms HighAnchorIntervalB.prime_power_error_bound
#print axioms HighAnchorIntervalB.interval_width_strict
