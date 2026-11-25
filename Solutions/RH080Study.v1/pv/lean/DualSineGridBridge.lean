/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import DualGridReal
import SineBridge
import AngleFolding

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH080PV.Grid
open Real Model
noncomputable section

theorem sine_step_identity : Model.sineStep = RH080.SineBridge.sineStep := rfl

theorem sine_model_identity : Model.sineFixed = RH080.SineBridge.sineFixed := by
  funext r
  simp only [Model.sineFixed,RH080.SineBridge.sineFixed,sine_step_identity]

theorem angle_model_identity (j k : Nat) :
    Model.reducedAngle j k = RH080.SineBridge.foldAngle (j*k) := rfl

theorem signedSine_error (j k : Nat) :
    |sin (π*j*k/256)-signedSine j k| ≤ 1/10000000 := by
  let r : Fin 129 := ⟨(reducedAngle j k).1, by have h := reducedAngle_mem j k; omega⟩
  have accuracy := RH080.SineBridge.sine_fixed_real_error r
  rw [←sine_model_identity] at accuracy
  have folded := RH080.SineBridge.sin_foldAngle (j*k)
  rw [←angle_model_identity] at folded
  have hm : π*((j*k:Nat):ℝ)/256 = π*j*k/256 := by push_cast; ring
  rw [hm] at folded
  rcases h : reducedAngle j k with ⟨index,flipped⟩
  have reduced : |(sineFixed index : ℝ)/1000000000 - sin (π*index/256)| ≤
      1/10000000 := by simpa [r,h] using accuracy
  rw [h] at folded
  cases flipped
  · simp only [Bool.false_eq_true,↓reduceIte] at folded
    rw [folded]
    simpa [signedSine,signedRaw,h,abs_sub_comm] using reduced
  · simp only [↓reduceIte] at folded
    rw [folded]
    convert reduced using 1 <;> simp [signedSine,signedRaw,h] <;> congr 1 <;> ring

theorem piLower_le_pi : (piLower : ℝ) ≤ π := by
  have h := Real.pi_gt_d20
  norm_num [piLower]
  linarith

/-- All256nonzero samples of the actual real inverse-transform numerator. The
source-C arithmetic model supplies the integer cap, while sine/pi are the actual
Mathlib real functions. No externally computed sine table is a hypothesis. -/
theorem true_grid_samples (k : Fin 257) (hk : k.val≠0) :
    |trigNumerator (k.val/128)/(π*k.val/128)| ≤
      (sampleBound k.val : ℝ)/1000000 := by
  apply grid_real_bound k hk piLower_le_pi
  intro j hj
  simpa only [Nat.cast_add,Nat.cast_one] using signedSine_error (j+1) k.val

theorem true_grid_uniform (k : Fin 257) (hk : k.val≠0) :
    |trigNumerator (k.val/128)/(π*k.val/128)| ≤ 1221161/1000000 := by
  have h := true_grid_samples k hk
  have cap := Model.sampleBound_all k
  have hc : (sampleBound k.val : ℝ) ≤ 1221161 := by exact_mod_cast cap
  linarith

#print axioms signedSine_error
#print axioms true_grid_uniform
end
end RH080PV.Grid
