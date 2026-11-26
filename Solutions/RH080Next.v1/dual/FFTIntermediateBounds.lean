/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import W4FFTGlobalTraceBounds
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open scoped BigOperators
namespace RH080Next.FFT.IntegerModel

theorem subsampled_mass_le (input : Nat → CInt) (s S index step : Nat)
    (hindex : index<step) (hsize : step*2^s=2^S) :
    coefficientMass (2^s) (fun j => decode (input (index+step*j)))≤
      coefficientMass (2^S) (fun j => decode (input j)) := by
  let f : Nat → Nat := fun j => index+step*j
  have hinj : Function.Injective f := by
    intro a b he
    exact mul_left_cancel₀ (show step≠0 by omega) (Nat.add_left_cancel he)
  have hsub : (Finset.range (2^s)).image f ⊆ Finset.range (2^S) := by
    intro k hk
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hk
    have hj' := Finset.mem_range.mp hj
    have hm := Nat.mul_le_mul_left step (Nat.succ_le_of_lt hj')
    apply Finset.mem_range.mpr
    dsimp [f]
    rw [←hsize]
    nlinarith
  unfold coefficientMass
  calc
    _ = ∑k ∈ (Finset.range (2^s)).image f, ‖decode (input k)‖ := by
      rw [Finset.sum_image]
      intro a ha b hb he
      exact hinj he
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => norm_nonneg _)

private theorem uniform_rounding_budget (s : Nat) (hs : s≤24) :
    (((1:ℝ)+1/10000000000000000000)^s-1)*362+
      ((2:ℝ)^s-1)*(1+1/10000000000000000000)^s*(4/(unit:ℝ))≤1 := by
  have ha : (1+(1/10000000000000000000:ℝ))^s≤(1+1/10000000000000000000)^24 :=
    pow_le_pow_right₀ (by norm_num) hs
  have hb : (2:ℝ)^s≤2^24 := pow_le_pow_right₀ (by norm_num) hs
  have hn : 0≤(2:ℝ)^s-1 := by have := one_le_pow₀ (n:=s) (by norm_num : (1:ℝ)≤2); linarith
  have hmul := mul_le_mul (sub_le_sub_right hb 1) ha (by positivity) (by positivity)
  have hlast := mul_le_mul_of_nonneg_right hmul (by norm_num [unit] : (0:ℝ)≤4/(unit:ℝ))
  have hfirst := mul_le_mul_of_nonneg_right (sub_le_sub_right ha 1) (by norm_num : (0:ℝ)≤362)
  have hnumeric : (((1:ℝ)+1/10000000000000000000)^24-1)*362+
      ((2:ℝ)^24-1)*(1+1/10000000000000000000)^24*(4/(unit:ℝ))≤1 := by norm_num [unit]
  linarith

/-- Every actual subtransform, not an assumption about C outputs. The source
refiner can use this theorem to discharge each subsequent helper's domain. -/
theorem ExecutionTrace.subtransform_norm_le {stages : Nat → List CInt}
    {input : Nat → CInt} {s S index step : Nat} {out : List CInt}
    (h : ExecutionTrace stages input s index step out) (hs : s≤S) (hS : S≤24)
    (hindex : index<step) (hsize : step*2^s=2^S)
    (hmass : coefficientMass (2^S) (fun j => decode (input j))≤362)
    (hw : ∀ t<S, ∀ j<2^t,
      ‖decode ((stages (t+1)).getD j (0,0))-negativeRoot (2*2^t)^j‖≤
        (1/10000000000000000000:ℝ))
    (k : Nat) (hk : k<2^s) : ‖decode (out.getD k (0,0))‖≤400 := by
  let f : Nat → ℂ := fun j => decode (input (index+step*j))
  have hm : coefficientMass (2^s) f≤362 := (subsampled_mass_le input s S index step hindex hsize).trans hmass
  have herr := roundedFFT_dft_error s f k hk
    (fun t j => decode ((stages t).getD j (0,0))) roundedComplex
    (1/10000000000000000000) (4/(unit:ℝ)) (by norm_num) (by norm_num [unit])
    (fun t ht j hj => hw t (by omega) j hj) roundedComplex_error
  rw [←h.decode_roundedFFT k hk] at herr
  have hpow : 0≤(1+(1/10000000000000000000:ℝ))^s-1 := by
    have := one_le_pow₀ (n:=s) (by norm_num : (1:ℝ)≤1+1/10000000000000000000)
    linarith
  have hm' := mul_le_mul_of_nonneg_left hm hpow
  have hb := uniform_rounding_budget s (by omega)
  have herr1 : ‖decode (out.getD k (0,0))-dftSum (2^s) k (negativeRoot (2^s)) f‖≤1 := by linarith
  have hd := (norm_dft_le_mass (2^s) k (negativeRoot (2^s)) f (negativeRoot_norm _)).trans hm
  have hh := norm_le_norm_sub_add (decode (out.getD k (0,0))) (dftSum (2^s) k (negativeRoot (2^s)) f)
  linarith

theorem stage_norm_le_two (stages : Nat → List CInt) (t j : Nat)
    (h : ‖decode ((stages (t+1)).getD j (0,0))-negativeRoot (2*2^t)^j‖≤
      (1/10000000000000000000:ℝ)) :
    ‖decode ((stages (t+1)).getD j (0,0))‖≤2 := by
  have hroot : ‖negativeRoot (2*2^t)^j‖=1 := by rw [norm_pow,negativeRoot_norm,one_pow]
  have hn := norm_le_norm_sub_add (decode ((stages (t+1)).getD j (0,0))) (negativeRoot (2*2^t)^j)
  rw [hroot] at hn
  linarith

theorem decoded_product_norm_le_801 (b w : CInt) (hb : ‖decode b‖≤400)
    (hw : ‖decode w‖≤2) : ‖decode (mul b w)‖≤801 := by
  rw [decode_mul]
  have h := roundedComplex_error (decode b) (decode w)
  have hn := norm_le_norm_sub_add (roundedComplex (decode b) (decode w)) (decode b*decode w)
  have hp : ‖decode b*decode w‖≤800 := by rw [norm_mul]; nlinarith [norm_nonneg (decode b),norm_nonneg (decode w)]
  have he : (4/(unit:ℝ))≤1 := by norm_num [unit]
  linarith

#print axioms ExecutionTrace.subtransform_norm_le
#print axioms stage_norm_le_two
#print axioms decoded_product_norm_le_801
end RH080Next.FFT.IntegerModel
