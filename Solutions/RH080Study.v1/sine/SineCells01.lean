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
theorem error016 : |(sineFixed 16 : ℚ)/1000000000 - polyQ ((3141592654*16/256 : Nat)/1000000000 : ℚ)| ≤ 1/50000000 := by
  norm_num [sineFixed, sineStep, polyQ, List.range_succ]

theorem error017 : |(sineFixed 17 : ℚ)/1000000000 - polyQ ((3141592654*17/256 : Nat)/1000000000 : ℚ)| ≤ 1/50000000 := by
  norm_num [sineFixed, sineStep, polyQ, List.range_succ]

theorem error018 : |(sineFixed 18 : ℚ)/1000000000 - polyQ ((3141592654*18/256 : Nat)/1000000000 : ℚ)| ≤ 1/50000000 := by
  norm_num [sineFixed, sineStep, polyQ, List.range_succ]

theorem error019 : |(sineFixed 19 : ℚ)/1000000000 - polyQ ((3141592654*19/256 : Nat)/1000000000 : ℚ)| ≤ 1/50000000 := by
  norm_num [sineFixed, sineStep, polyQ, List.range_succ]

theorem error020 : |(sineFixed 20 : ℚ)/1000000000 - polyQ ((3141592654*20/256 : Nat)/1000000000 : ℚ)| ≤ 1/50000000 := by
  norm_num [sineFixed, sineStep, polyQ, List.range_succ]

theorem error021 : |(sineFixed 21 : ℚ)/1000000000 - polyQ ((3141592654*21/256 : Nat)/1000000000 : ℚ)| ≤ 1/50000000 := by
  norm_num [sineFixed, sineStep, polyQ, List.range_succ]

theorem error022 : |(sineFixed 22 : ℚ)/1000000000 - polyQ ((3141592654*22/256 : Nat)/1000000000 : ℚ)| ≤ 1/50000000 := by
  norm_num [sineFixed, sineStep, polyQ, List.range_succ]

theorem error023 : |(sineFixed 23 : ℚ)/1000000000 - polyQ ((3141592654*23/256 : Nat)/1000000000 : ℚ)| ≤ 1/50000000 := by
  norm_num [sineFixed, sineStep, polyQ, List.range_succ]

theorem error024 : |(sineFixed 24 : ℚ)/1000000000 - polyQ ((3141592654*24/256 : Nat)/1000000000 : ℚ)| ≤ 1/50000000 := by
  norm_num [sineFixed, sineStep, polyQ, List.range_succ]

theorem error025 : |(sineFixed 25 : ℚ)/1000000000 - polyQ ((3141592654*25/256 : Nat)/1000000000 : ℚ)| ≤ 1/50000000 := by
  norm_num [sineFixed, sineStep, polyQ, List.range_succ]

theorem error026 : |(sineFixed 26 : ℚ)/1000000000 - polyQ ((3141592654*26/256 : Nat)/1000000000 : ℚ)| ≤ 1/50000000 := by
  norm_num [sineFixed, sineStep, polyQ, List.range_succ]

theorem error027 : |(sineFixed 27 : ℚ)/1000000000 - polyQ ((3141592654*27/256 : Nat)/1000000000 : ℚ)| ≤ 1/50000000 := by
  norm_num [sineFixed, sineStep, polyQ, List.range_succ]

theorem error028 : |(sineFixed 28 : ℚ)/1000000000 - polyQ ((3141592654*28/256 : Nat)/1000000000 : ℚ)| ≤ 1/50000000 := by
  norm_num [sineFixed, sineStep, polyQ, List.range_succ]

theorem error029 : |(sineFixed 29 : ℚ)/1000000000 - polyQ ((3141592654*29/256 : Nat)/1000000000 : ℚ)| ≤ 1/50000000 := by
  norm_num [sineFixed, sineStep, polyQ, List.range_succ]

theorem error030 : |(sineFixed 30 : ℚ)/1000000000 - polyQ ((3141592654*30/256 : Nat)/1000000000 : ℚ)| ≤ 1/50000000 := by
  norm_num [sineFixed, sineStep, polyQ, List.range_succ]

theorem error031 : |(sineFixed 31 : ℚ)/1000000000 - polyQ ((3141592654*31/256 : Nat)/1000000000 : ℚ)| ≤ 1/50000000 := by
  norm_num [sineFixed, sineStep, polyQ, List.range_succ]
end RH080.SineBridge
