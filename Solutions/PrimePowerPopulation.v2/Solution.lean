/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Nodes.PrimePowerPopulation.v2.Conclusions
import SameSourceTiling
set_option autoImplicit false
namespace PrimePowerPopulation.v2
open Real

theorem challenge_cube_density_all_real (hf:PrimeInterval.v4.optimized_strict_family) :
    cube_density_all_real := by
  intro n hn
  exact RH080.SameSource.cube_density_078146 hf hn

theorem challenge_single_window_cube (hf:PrimeInterval.v4.optimized_strict_family) :
    single_window_cube := by
  intro n hn hC
  exact RH080.SameSource.single_window_078146 hf hn hC

theorem challenge_equal_cell_cube (hf:PrimeInterval.v4.optimized_strict_family) :
    equal_cell_cube := by
  intro n hn hC
  exact RH080.SameSource.tiled_0789 hf hn hC

theorem challenge_equal_cell_cube_late (hf:PrimeInterval.v4.optimized_strict_family) :
    equal_cell_cube_late := by
  intro n hn hC hL
  exact RH080.SameSource.tiled_0804_late hf hn hC hL

private theorem exp8_lt_2981 : exp 8<(2981:ℝ) := by
  have he:exp 1≤(27182818286/10000000000:ℝ):=Real.exp_one_lt_d9.le.trans (by norm_num)
  have hp:=pow_le_pow_left₀ (exp_nonneg 1) he 8
  rw [←exp_nat_mul] at hp
  norm_num at hp
  linarith

theorem challenge_cube_density_natural (hf:PrimeInterval.v4.optimized_strict_family) :
    cube_density_natural := by
  intro n hn
  have hnR:(2981:ℝ)≤n:=by exact_mod_cast hn
  exact challenge_cube_density_all_real hf n (exp8_lt_2981.le.trans hnR)

theorem challenge_strict_coefficient_gain : strict_coefficient_gain := by
  intro n hn
  have hn0:0<n:=(exp_pos _).trans_le hn
  have hL:8≤log n:=by simpa using log_le_log (exp_pos 8) hn
  apply (div_lt_div_iff_of_pos_right (show 0<log n by linarith)).mpr
  nlinarith [sq_pos_of_pos hn0]

theorem challenge_retains_070_all_real (hf:PrimeInterval.v4.optimized_strict_family) :
    retains_070_all_real := by
  intro n hn
  exact (challenge_strict_coefficient_gain n hn).trans (challenge_cube_density_all_real hf n hn)
end PrimePowerPopulation.v2
#print axioms PrimePowerPopulation.v2.challenge_cube_density_all_real
#print axioms PrimePowerPopulation.v2.challenge_single_window_cube
#print axioms PrimePowerPopulation.v2.challenge_equal_cell_cube
#print axioms PrimePowerPopulation.v2.challenge_equal_cell_cube_late
#print axioms PrimePowerPopulation.v2.challenge_cube_density_natural
#print axioms PrimePowerPopulation.v2.challenge_strict_coefficient_gain
#print axioms PrimePowerPopulation.v2.challenge_retains_070_all_real
