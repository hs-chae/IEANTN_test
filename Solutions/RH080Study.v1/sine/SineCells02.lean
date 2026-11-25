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
theorem error032 : |(sineFixed 32 : ℚ)/1000000000 - polyQ ((3141592654*32/256 : Nat)/1000000000 : ℚ)| ≤ 1/50000000 := by
  norm_num [sineFixed, sineStep, polyQ, List.range_succ]

theorem error033 : |(sineFixed 33 : ℚ)/1000000000 - polyQ ((3141592654*33/256 : Nat)/1000000000 : ℚ)| ≤ 1/50000000 := by
  norm_num [sineFixed, sineStep, polyQ, List.range_succ]

theorem error034 : |(sineFixed 34 : ℚ)/1000000000 - polyQ ((3141592654*34/256 : Nat)/1000000000 : ℚ)| ≤ 1/50000000 := by
  norm_num [sineFixed, sineStep, polyQ, List.range_succ]

theorem error035 : |(sineFixed 35 : ℚ)/1000000000 - polyQ ((3141592654*35/256 : Nat)/1000000000 : ℚ)| ≤ 1/50000000 := by
  norm_num [sineFixed, sineStep, polyQ, List.range_succ]

theorem error036 : |(sineFixed 36 : ℚ)/1000000000 - polyQ ((3141592654*36/256 : Nat)/1000000000 : ℚ)| ≤ 1/50000000 := by
  norm_num [sineFixed, sineStep, polyQ, List.range_succ]

theorem error037 : |(sineFixed 37 : ℚ)/1000000000 - polyQ ((3141592654*37/256 : Nat)/1000000000 : ℚ)| ≤ 1/50000000 := by
  norm_num [sineFixed, sineStep, polyQ, List.range_succ]

theorem error038 : |(sineFixed 38 : ℚ)/1000000000 - polyQ ((3141592654*38/256 : Nat)/1000000000 : ℚ)| ≤ 1/50000000 := by
  norm_num [sineFixed, sineStep, polyQ, List.range_succ]

theorem error039 : |(sineFixed 39 : ℚ)/1000000000 - polyQ ((3141592654*39/256 : Nat)/1000000000 : ℚ)| ≤ 1/50000000 := by
  norm_num [sineFixed, sineStep, polyQ, List.range_succ]

theorem error040 : |(sineFixed 40 : ℚ)/1000000000 - polyQ ((3141592654*40/256 : Nat)/1000000000 : ℚ)| ≤ 1/50000000 := by
  norm_num [sineFixed, sineStep, polyQ, List.range_succ]

theorem error041 : |(sineFixed 41 : ℚ)/1000000000 - polyQ ((3141592654*41/256 : Nat)/1000000000 : ℚ)| ≤ 1/50000000 := by
  norm_num [sineFixed, sineStep, polyQ, List.range_succ]

theorem error042 : |(sineFixed 42 : ℚ)/1000000000 - polyQ ((3141592654*42/256 : Nat)/1000000000 : ℚ)| ≤ 1/50000000 := by
  norm_num [sineFixed, sineStep, polyQ, List.range_succ]

theorem error043 : |(sineFixed 43 : ℚ)/1000000000 - polyQ ((3141592654*43/256 : Nat)/1000000000 : ℚ)| ≤ 1/50000000 := by
  norm_num [sineFixed, sineStep, polyQ, List.range_succ]

theorem error044 : |(sineFixed 44 : ℚ)/1000000000 - polyQ ((3141592654*44/256 : Nat)/1000000000 : ℚ)| ≤ 1/50000000 := by
  norm_num [sineFixed, sineStep, polyQ, List.range_succ]

theorem error045 : |(sineFixed 45 : ℚ)/1000000000 - polyQ ((3141592654*45/256 : Nat)/1000000000 : ℚ)| ≤ 1/50000000 := by
  norm_num [sineFixed, sineStep, polyQ, List.range_succ]

theorem error046 : |(sineFixed 46 : ℚ)/1000000000 - polyQ ((3141592654*46/256 : Nat)/1000000000 : ℚ)| ≤ 1/50000000 := by
  norm_num [sineFixed, sineStep, polyQ, List.range_succ]

theorem error047 : |(sineFixed 47 : ℚ)/1000000000 - polyQ ((3141592654*47/256 : Nat)/1000000000 : ℚ)| ≤ 1/50000000 := by
  norm_num [sineFixed, sineStep, polyQ, List.range_succ]
end RH080.SineBridge
