/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import SineSpec
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace RH080.SineBridge
theorem error000 : |(sineFixed 0 : ℚ)/1000000000 - polyQ ((3141592654*0/256 : Nat)/1000000000 : ℚ)| ≤ 1/50000000 := by
  norm_num [sineFixed, sineStep, polyQ, List.range_succ]

theorem error001 : |(sineFixed 1 : ℚ)/1000000000 - polyQ ((3141592654*1/256 : Nat)/1000000000 : ℚ)| ≤ 1/50000000 := by
  norm_num [sineFixed, sineStep, polyQ, List.range_succ]

theorem error002 : |(sineFixed 2 : ℚ)/1000000000 - polyQ ((3141592654*2/256 : Nat)/1000000000 : ℚ)| ≤ 1/50000000 := by
  norm_num [sineFixed, sineStep, polyQ, List.range_succ]

theorem error003 : |(sineFixed 3 : ℚ)/1000000000 - polyQ ((3141592654*3/256 : Nat)/1000000000 : ℚ)| ≤ 1/50000000 := by
  norm_num [sineFixed, sineStep, polyQ, List.range_succ]

theorem error004 : |(sineFixed 4 : ℚ)/1000000000 - polyQ ((3141592654*4/256 : Nat)/1000000000 : ℚ)| ≤ 1/50000000 := by
  norm_num [sineFixed, sineStep, polyQ, List.range_succ]

theorem error005 : |(sineFixed 5 : ℚ)/1000000000 - polyQ ((3141592654*5/256 : Nat)/1000000000 : ℚ)| ≤ 1/50000000 := by
  norm_num [sineFixed, sineStep, polyQ, List.range_succ]

theorem error006 : |(sineFixed 6 : ℚ)/1000000000 - polyQ ((3141592654*6/256 : Nat)/1000000000 : ℚ)| ≤ 1/50000000 := by
  norm_num [sineFixed, sineStep, polyQ, List.range_succ]

theorem error007 : |(sineFixed 7 : ℚ)/1000000000 - polyQ ((3141592654*7/256 : Nat)/1000000000 : ℚ)| ≤ 1/50000000 := by
  norm_num [sineFixed, sineStep, polyQ, List.range_succ]

theorem error008 : |(sineFixed 8 : ℚ)/1000000000 - polyQ ((3141592654*8/256 : Nat)/1000000000 : ℚ)| ≤ 1/50000000 := by
  norm_num [sineFixed, sineStep, polyQ, List.range_succ]

theorem error009 : |(sineFixed 9 : ℚ)/1000000000 - polyQ ((3141592654*9/256 : Nat)/1000000000 : ℚ)| ≤ 1/50000000 := by
  norm_num [sineFixed, sineStep, polyQ, List.range_succ]

theorem error010 : |(sineFixed 10 : ℚ)/1000000000 - polyQ ((3141592654*10/256 : Nat)/1000000000 : ℚ)| ≤ 1/50000000 := by
  norm_num [sineFixed, sineStep, polyQ, List.range_succ]

theorem error011 : |(sineFixed 11 : ℚ)/1000000000 - polyQ ((3141592654*11/256 : Nat)/1000000000 : ℚ)| ≤ 1/50000000 := by
  norm_num [sineFixed, sineStep, polyQ, List.range_succ]

theorem error012 : |(sineFixed 12 : ℚ)/1000000000 - polyQ ((3141592654*12/256 : Nat)/1000000000 : ℚ)| ≤ 1/50000000 := by
  norm_num [sineFixed, sineStep, polyQ, List.range_succ]

theorem error013 : |(sineFixed 13 : ℚ)/1000000000 - polyQ ((3141592654*13/256 : Nat)/1000000000 : ℚ)| ≤ 1/50000000 := by
  norm_num [sineFixed, sineStep, polyQ, List.range_succ]

theorem error014 : |(sineFixed 14 : ℚ)/1000000000 - polyQ ((3141592654*14/256 : Nat)/1000000000 : ℚ)| ≤ 1/50000000 := by
  norm_num [sineFixed, sineStep, polyQ, List.range_succ]

theorem error015 : |(sineFixed 15 : ℚ)/1000000000 - polyQ ((3141592654*15/256 : Nat)/1000000000 : ℚ)| ≤ 1/50000000 := by
  norm_num [sineFixed, sineStep, polyQ, List.range_succ]
end RH080.SineBridge
