/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Nodes.ThetaCubePopulation.v1.Conclusions
import IEANTN.Nodes.SchoenfeldRHTheta.v1.Conclusions
import IEANTN.Nodes.Buthe.v1.Conclusions
import IEANTN.Nodes.RH.v1.Conclusions
import CubeRefined
set_option autoImplicit false
namespace ThetaCubePopulation.v1
open Real

private theorem schoenfeld_adapter (h : SchoenfeldRHTheta.v1.refined_theta) :
    RH080.Estimates.SchoenfeldTheta61 := by
  simpa only [SchoenfeldRHTheta.v1.refined_theta, IEANTN.ThetaWindows.schoenfeldError,
    RH080.Estimates.SchoenfeldTheta61] using h

private theorem buthe_adapter (h₁ : Buthe.v1.theorem_2_theta)
    (h₂ : Buthe.v1.theorem_2_theta_lower) : RH080.Estimates.ButheTheta1617 := by
  constructor
  · simpa only [Buthe.v1.theorem_2_theta, show (1.95:ℝ) = 39/20 by norm_num] using h₁
  · simpa only [Buthe.v1.theorem_2_theta_lower, show (0.05:ℝ) = 1/20 by norm_num] using h₂

theorem challenge_schoenfeld_cube_curve (hRH : RH.v1.hypothesis)
    (hS : SchoenfeldRHTheta.v1.refined_theta) : schoenfeld_cube_curve := by
  intro n hn
  simpa only [IEANTN.ThetaWindows.cubeSchoenfeldLower,
    IEANTN.ThetaWindows.schoenfeldError,IEANTN.ThetaWindows.openPrimes,
    RH080.Estimates.openPrimes] using
    RH080.Estimates.cube_count_schoenfeld_explicit (schoenfeld_adapter hS) hRH hn

theorem challenge_buthe_cube_curve (h₁ : Buthe.v1.theorem_2_theta)
    (h₂ : Buthe.v1.theorem_2_theta_lower) : buthe_cube_curve := by
  intro n hn hhi
  simpa only [IEANTN.ThetaWindows.cubeButheLower,IEANTN.ThetaWindows.openPrimes,
    RH080.Estimates.openPrimes] using
    RH080.Estimates.cube_count_buthe_explicit (buthe_adapter h₁ h₂) hn hhi

theorem challenge_cube_density_096 (hRH : RH.v1.hypothesis)
    (hS : SchoenfeldRHTheta.v1.refined_theta) (h₁ : Buthe.v1.theorem_2_theta)
    (h₂ : Buthe.v1.theorem_2_theta_lower) : cube_density_096 := by
  intro n hn
  simpa only [IEANTN.ThetaWindows.openPrimes,RH080.Estimates.openPrimes] using
    RH080.Estimates.cube_density_096 (buthe_adapter h₁ h₂) (schoenfeld_adapter hS) hRH hn

theorem challenge_cube_density_0965 (hRH : RH.v1.hypothesis)
    (hS : SchoenfeldRHTheta.v1.refined_theta) (h₁ : Buthe.v1.theorem_2_theta)
    (h₂ : Buthe.v1.theorem_2_theta_lower) : cube_density_0965 := by
  intro n hn
  simpa only [IEANTN.ThetaWindows.openPrimes,RH080.Estimates.openPrimes] using
    RH080.Estimates.cube_density_0965 (buthe_adapter h₁ h₂) (schoenfeld_adapter hS) hRH hn

theorem challenge_cube_density_0965_finite (h₁ : Buthe.v1.theorem_2_theta)
    (h₂ : Buthe.v1.theorem_2_theta_lower) : cube_density_0965_finite := by
  intro n hn hhi
  simpa only [IEANTN.ThetaWindows.openPrimes,RH080.Estimates.openPrimes] using
    RH080.Estimates.cube_density_0965_finite (buthe_adapter h₁ h₂) hn hhi

private theorem exp6_lt_404 : exp 6 < (404:ℝ) := by
  have he : exp 1 ≤ (27183/10000:ℝ) := Real.exp_one_lt_d9.le.trans (by norm_num)
  have hp := pow_le_pow_left₀ (exp_nonneg 1) he 6
  rw [←exp_nat_mul] at hp
  norm_num at hp
  linarith

theorem challenge_cube_density_0965_natural (hRH : RH.v1.hypothesis)
    (hS : SchoenfeldRHTheta.v1.refined_theta) (h₁ : Buthe.v1.theorem_2_theta)
    (h₂ : Buthe.v1.theorem_2_theta_lower) : cube_density_0965_natural := by
  intro n hn
  have hnR : (404:ℝ) ≤ n := by exact_mod_cast hn
  exact challenge_cube_density_0965 hRH hS h₁ h₂ n (exp6_lt_404.le.trans hnR)

theorem challenge_improves_old_coefficient : improves_old_coefficient := by
  intro n hn
  have hn0 : 0 < n := (exp_pos _).trans_le hn
  have hL : 8 ≤ log n := by simpa using log_le_log (exp_pos 8) hn
  apply (div_lt_div_iff_of_pos_right (show 0 < log n by linarith)).mpr
  nlinarith [sq_pos_of_pos hn0]

end ThetaCubePopulation.v1
#print axioms ThetaCubePopulation.v1.challenge_schoenfeld_cube_curve
#print axioms ThetaCubePopulation.v1.challenge_buthe_cube_curve
#print axioms ThetaCubePopulation.v1.challenge_cube_density_096
#print axioms ThetaCubePopulation.v1.challenge_cube_density_0965
#print axioms ThetaCubePopulation.v1.challenge_cube_density_0965_finite
#print axioms ThetaCubePopulation.v1.challenge_cube_density_0965_natural
#print axioms ThetaCubePopulation.v1.challenge_improves_old_coefficient
