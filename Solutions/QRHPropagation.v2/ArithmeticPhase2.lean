/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Frontier
namespace QRHPhase2
open Real IEANTN

theorem lcm_log_window (hpsi : QRHCH2.v2.psi_density_frontier)
    (n : ℕ) (hn : exp 192 ≤ (n : ℝ)) :
    |log (Nat.lcmUpto n : ℝ) - n| ≤ 0.01713 * (n : ℝ) ^ (7 / 8 : ℝ) := by
  have hn0 : 0 < (n : ℝ) := (exp_pos (192 : ℝ)).trans_le hn
  have hb := hpsi 192 0.01713 (by norm_num [CH2.v6.densityFrontier]) (n : ℝ) hn
  try simp only [pow_zero, mul_one] at hb
  rw [rpow_def_of_pos hn0] at hb
  have he : Real.exp (Real.log (n : ℝ) * (-1 / 8)) = (n : ℝ) ^ (7 / 8 : ℝ) / n := by
    rw [rpow_def_of_pos hn0, ← Real.exp_log hn0, ← Real.exp_sub, Real.log_exp]
    congr 1; ring
  have he' : Real.exp (Real.log (n : ℝ) * ((7 / 8 : ℝ) - 1)) = (n : ℝ) ^ (7 / 8 : ℝ) / n := by
    convert he using 1 <;> congr 1 <;> ring
  first | rw [he] at hb | rw [he'] at hb
  have hid : Eψ (n : ℝ) = |Chebyshev.psi (n : ℝ) - n| / n := rfl
  rw [hid] at hb
  have hh := (div_le_iff₀ hn0).mp hb
  have hresult : |Chebyshev.psi (n : ℝ) - n| ≤ 0.01713 * (n : ℝ) ^ (7 / 8 : ℝ) := by
    convert hh using 1 <;> first | rfl | field_simp
  rw [Chebyshev.psi_eq_log_lcmUpto] at hresult
  simpa using hresult

theorem primorial_log_window (hpsi : QRHCH2.v2.psi_density_frontier)
    (n : ℕ) (hn : exp 192 ≤ (n : ℝ)) :
    |log (primorial n : ℝ) - n| ≤ 0.01714 * (n : ℝ) ^ (7 / 8 : ℝ) := by
  have hn0 : 0 < (n : ℝ) := (exp_pos (192 : ℝ)).trans_le hn
  have hb := theta_192 hpsi (n : ℝ) hn
  try simp only [pow_zero, mul_one] at hb
  rw [rpow_def_of_pos hn0] at hb
  have he : Real.exp (Real.log (n : ℝ) * (-1 / 8)) = (n : ℝ) ^ (7 / 8 : ℝ) / n := by
    rw [rpow_def_of_pos hn0, ← Real.exp_log hn0, ← Real.exp_sub, Real.log_exp]
    congr 1; ring
  have he' : Real.exp (Real.log (n : ℝ) * ((7 / 8 : ℝ) - 1)) = (n : ℝ) ^ (7 / 8 : ℝ) / n := by
    convert he using 1 <;> congr 1 <;> ring
  first | rw [he] at hb | rw [he'] at hb
  have hid : Eθ (n : ℝ) = |Chebyshev.theta (n : ℝ) - n| / n := rfl
  rw [hid] at hb
  have hh := (div_le_iff₀ hn0).mp hb
  have hresult : |Chebyshev.theta (n : ℝ) - n| ≤ 0.01714 * (n : ℝ) ^ (7 / 8 : ℝ) := by
    convert hh using 1 <;> first | rfl | field_simp
  rw [Chebyshev.theta_eq_log_primorial] at hresult
  simpa using hresult

theorem arithmetic_width_strict {C x : ℝ} (hC : 0 ≤ C) (hC' : C ≤ 0.01714)
    (hx : exp 192 ≤ x) :
    C * x ^ (7 / 8 : ℝ) < (Real.pi / (3e12 : ℝ)) * x := by
  have hx0 : 0 < x := (exp_pos (192 : ℝ)).trans_le hx
  have hL : (192 : ℝ) ≤ log x := by
    have hh := log_le_log (exp_pos (192 : ℝ)) hx
    simpa using hh
  have hp : x ^ ((7 / 8 : ℝ) - 1) ≤ exp (-24) := by
    rw [rpow_def_of_pos hx0]
    exact exp_le_exp.mpr (by nlinarith)
  have hsmall : C * x ^ ((7 / 8 : ℝ) - 1) < 1 / (1e12 : ℝ) := by
    calc
      _ ≤ 0.01714 * exp (-24) := mul_le_mul hC' hp (rpow_pos_of_pos hx0 _).le (by norm_num)
      _ ≤ 0.01714 * (10 / 27 : ℝ) ^ 24 := by
        gcongr
        exact QRHPropagation.exp_neg_nat_upper 24
      _ < _ := by norm_num
  have hpi : (1 / (1e12 : ℝ)) < Real.pi / (3e12 : ℝ) := by
    linarith [Real.pi_gt_three]
  have hh := mul_lt_mul_of_pos_right (hsmall.trans hpi) hx0
  rw [rpow_sub hx0, rpow_one] at hh
  convert hh using 1 <;> first | rfl | field_simp
end QRHPhase2
