/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Nodes.ThetaCubePopulation.v2.Conclusions
import IEANTN.Nodes.SchoenfeldRHTheta.v1.Conclusions
import IEANTN.Nodes.Buthe.v1.Conclusions
import IEANTN.Nodes.RH.v1.Conclusions
import ParetoCube
set_option autoImplicit false
namespace ThetaCubePopulation.v2
open Real
private theorem schoenfeld_adapter (h:SchoenfeldRHTheta.v1.refined_theta) :
    RH080.Estimates.SchoenfeldTheta61 := by
  simpa only [SchoenfeldRHTheta.v1.refined_theta,IEANTN.ThetaWindows.schoenfeldError,
    RH080.Estimates.SchoenfeldTheta61] using h
private theorem buthe_adapter (h₁:Buthe.v1.theorem_2_theta)
    (h₂:Buthe.v1.theorem_2_theta_lower) : RH080.Estimates.ButheTheta1617 := by
  constructor
  · simpa only [Buthe.v1.theorem_2_theta,show (1.95:ℝ)=39/20 by norm_num] using h₁
  · simpa only [Buthe.v1.theorem_2_theta_lower,show (0.05:ℝ)=1/20 by norm_num] using h₂

theorem challenge_cube_density_09669924 (hRH:RH.v1.hypothesis)
    (hS:SchoenfeldRHTheta.v1.refined_theta) (h₁:Buthe.v1.theorem_2_theta)
    (h₂:Buthe.v1.theorem_2_theta_lower) : cube_density_09669924 := by
  intro n hn
  simpa only [IEANTN.ThetaWindows.openPrimes,RH080.Estimates.openPrimes] using
    RH080.Pareto966.cube_density_09669924 (buthe_adapter h₁ h₂) (schoenfeld_adapter hS) hRH hn

private theorem exp8_lt_2981 : exp 8<(2981:ℝ) := by
  have he:exp 1≤(27182818286/10000000000:ℝ):=Real.exp_one_lt_d9.le.trans (by norm_num)
  have hp:=pow_le_pow_left₀ (exp_nonneg 1) he 8
  rw [←exp_nat_mul] at hp
  norm_num at hp
  linarith

theorem challenge_cube_density_09669924_natural (hRH:RH.v1.hypothesis)
    (hS:SchoenfeldRHTheta.v1.refined_theta) (h₁:Buthe.v1.theorem_2_theta)
    (h₂:Buthe.v1.theorem_2_theta_lower) : cube_density_09669924_natural := by
  intro n hn
  have hnR:(2981:ℝ)≤n:=by exact_mod_cast hn
  exact challenge_cube_density_09669924 hRH hS h₁ h₂ n (exp8_lt_2981.le.trans hnR)

theorem challenge_finite_seam_098 (h₁:Buthe.v1.theorem_2_theta)
    (h₂:Buthe.v1.theorem_2_theta_lower) : finite_seam_098 := by
  intro n hn hhi
  simpa only [IEANTN.ThetaWindows.openPrimes,RH080.Estimates.openPrimes] using
    RH080.Pareto966.finite_098 (buthe_adapter h₁ h₂) hn hhi

theorem challenge_strict_gain_on_common_ray : strict_gain_on_common_ray := by
  intro n hn
  have hn0:0<n:=(exp_pos _).trans_le hn
  have hL:8≤log n:=by simpa using log_le_log (exp_pos 8) hn
  apply (div_lt_div_iff_of_pos_right (show 0<log n by linarith)).mpr
  nlinarith [sq_pos_of_pos hn0]

theorem challenge_retains_0965 (hOld:ThetaCubePopulation.v1.cube_density_0965) :
    retains_0965 := hOld
end ThetaCubePopulation.v2
#print axioms ThetaCubePopulation.v2.challenge_cube_density_09669924
#print axioms ThetaCubePopulation.v2.challenge_cube_density_09669924_natural
#print axioms ThetaCubePopulation.v2.challenge_finite_seam_098
#print axioms ThetaCubePopulation.v2.challenge_strict_gain_on_common_ray
#print axioms ThetaCubePopulation.v2.challenge_retains_0965
