/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Nodes.ThetaCubePopulation.v3.Conclusions
import IEANTN.Nodes.SchoenfeldRHTheta.v1.Conclusions
import IEANTN.Nodes.Buthe.v1.Conclusions
import IEANTN.Nodes.RH.v1.Conclusions
import CubeTheta
set_option autoImplicit false
namespace ThetaCubePopulation.v3
open Real
private theorem schoenfeld_adapter (h:SchoenfeldRHTheta.v1.refined_theta) :
    CubeTheta.Schoenfeld61 := by
  simpa only [SchoenfeldRHTheta.v1.refined_theta,IEANTN.ThetaWindows.schoenfeldError,
    CubeTheta.Schoenfeld61,CubeTheta.err] using h
private theorem buthe_adapter (h₁:Buthe.v1.theorem_2_theta)
    (h₂:Buthe.v1.theorem_2_theta_lower) : CubeTheta.Buthe1617 := by
  constructor
  · simpa only [Buthe.v1.theorem_2_theta,show (1.95:ℝ)=195/100 by norm_num] using h₁
  · simpa only [Buthe.v1.theorem_2_theta_lower,show (0.05:ℝ)=5/100 by norm_num] using h₂

theorem challenge_cube_density_096699_from_369 (hRH:RH.v1.hypothesis)
    (hS:SchoenfeldRHTheta.v1.refined_theta) (h₁:Buthe.v1.theorem_2_theta)
    (h₂:Buthe.v1.theorem_2_theta_lower) : cube_density_096699_from_369 := by
  intro n hn
  simpa only [IEANTN.ThetaWindows.openPrimes,CubeTheta.count,QuarticWindow.primesBetween,
    show (0.96699:ℝ)=96699/100000 by norm_num] using
    CubeTheta.cube_hybrid_096699 (schoenfeld_adapter hS) hRH (buthe_adapter h₁ h₂) hn

theorem challenge_cube_density_096699_natural (hRH:RH.v1.hypothesis)
    (hS:SchoenfeldRHTheta.v1.refined_theta) (h₁:Buthe.v1.theorem_2_theta)
    (h₂:Buthe.v1.theorem_2_theta_lower) : cube_density_096699_natural := by
  intro n hn
  have hnR:(369:ℝ)≤n:=by exact_mod_cast hn
  exact challenge_cube_density_096699_from_369 hRH hS h₁ h₂ n hnR

theorem challenge_hybrid_density (hEarly:cube_density_096699_from_369)
    (hLate:ThetaCubePopulation.v2.cube_density_09669924) : hybrid_density := by
  intro n hn
  by_cases h:exp 8≤n
  · simpa only [if_pos h] using hLate n h
  · simpa only [if_neg h] using hEarly n hn

theorem challenge_strict_gain_on_common_ray : strict_gain_on_common_ray := by
  intro n hn
  have hn0:0<n:=(exp_pos _).trans_le hn
  have hL:6≤log n:=by simpa using log_le_log (exp_pos 6) hn
  apply (div_lt_div_iff_of_pos_right (show 0<log n by linarith)).mpr
  nlinarith [sq_pos_of_pos hn0]
end ThetaCubePopulation.v3
#print axioms ThetaCubePopulation.v3.challenge_cube_density_096699_from_369
#print axioms ThetaCubePopulation.v3.challenge_cube_density_096699_natural
#print axioms ThetaCubePopulation.v3.challenge_hybrid_density
#print axioms ThetaCubePopulation.v3.challenge_strict_gain_on_common_ray
