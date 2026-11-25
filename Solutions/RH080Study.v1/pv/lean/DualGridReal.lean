/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import DualGridArithmetic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH080PV.Grid
open Model Real
noncomputable section

def signedRaw (j k : Nat) : ℝ :=
  let (r,flipped) := reducedAngle j k
  if flipped then -(sineFixed r : ℝ) else (sineFixed r : ℝ)

def signedSine (j k : Nat) : ℝ := signedRaw j k / 1000000000
def coefficient (j : Nat) : ℝ := ((positiveJump j : ℝ)-negativeJump j)/256

def trigNumerator (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range 20, coefficient (j+1) * sin (π*(j+1)*x/2)

lemma pointStep_signed (k : Nat) (state : Nat × Nat) (i : Nat) :
    ((pointStep k state i).1 : ℝ) - (pointStep k state i).2 =
      ((state.1 : ℝ)-state.2) +
      ((positiveJump (i+1) : ℝ)-negativeJump (i+1))*signedRaw (i+1) k := by
  rcases h : reducedAngle (i+1) k with ⟨r,flipped⟩
  cases flipped <;> simp [pointStep,signedRaw,h] <;> push_cast <;> ring

lemma fold_signed (k : Nat) (xs : List Nat) (state : Nat × Nat) :
    (((xs.foldl (pointStep k) state).1 : ℝ) -
      (xs.foldl (pointStep k) state).2) =
    ((state.1 : ℝ)-state.2) +
      (xs.map fun i => ((positiveJump (i+1) : ℝ)-negativeJump (i+1))*
        signedRaw (i+1) k).sum := by
  induction xs generalizing state with
  | nil => simp
  | cons i xs ih =>
    simp only [List.foldl_cons,List.map_cons,List.sum_cons,ih,pointStep_signed]
    ring

lemma sum_range_list (n : Nat) (f : Nat → ℝ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ,Finset.sum_range_succ,ih]

theorem approximateNumerator_identity (k : Nat) :
    (approximateNumerator k : ℝ) =
      ∑ j ∈ Finset.range 20, coefficient (j+1)*signedSine (j+1) k := by
  have h := fold_signed k (List.range 20) (0,0)
  simp only [Nat.cast_zero,sub_self,zero_add] at h
  rw [sum_range_list] at h
  simp only [approximateNumerator,accumulator]
  push_cast
  rw [h]
  simp only [coefficient,signedSine]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem coefficient_abs_sum :
    (∑ j ∈ Finset.range 20, |coefficient (j+1)|) = 3192/256 := by
  norm_num [coefficient,positiveJump,negativeJump,Finset.sum_range_succ]

theorem absoluteAccumulator_identity (k : Nat) :
    (absoluteAccumulator k : ℝ) =
      |((accumulator k).1 : ℝ)-(accumulator k).2| := by
  simp only [absoluteAccumulator]
  split_ifs with h
  · rw [Nat.cast_sub h, abs_of_nonneg]
    exact sub_nonneg.mpr (by exact_mod_cast h)
  · have hrev : (accumulator k).1 ≤ (accumulator k).2 := by omega
    rw [Nat.cast_sub hrev,abs_of_nonpos]
    · ring
    · exact sub_nonpos.mpr (by exact_mod_cast hrev)

theorem approximateNumerator_abs (k : Nat) :
    |(approximateNumerator k : ℝ)| =
      (absoluteAccumulator k : ℝ)/256000000000 := by
  simp only [approximateNumerator]
  push_cast
  rw [abs_div,←absoluteAccumulator_identity]
  norm_num

/-- The only analytic pointwise input is a real sine-error claim. The following
closed adapter instantiates it with the separately proved angle-folding and
129-point sine theorem; no literature or program-output premise is hidden here. -/
theorem numerator_error (k : Nat)
    (errors : ∀ j ∈ Finset.range 20,
      |sin (π*(j+1)*k/256)-signedSine (j+1) k| ≤ 1/10000000) :
    |trigNumerator (k/128) - (approximateNumerator k : ℝ)| ≤
      (3192/256)*(1/10000000) := by
  have harg (j : Nat) : π*(j+1)*((k:ℝ)/128)/2 = π*(j+1)*k/256 := by ring
  rw [trigNumerator,approximateNumerator_identity,←Finset.sum_sub_distrib]
  simp_rw [harg]
  calc
    |∑ j ∈ Finset.range 20,
        (coefficient (j+1)*sin (π*(j+1)*k/256)-
          coefficient (j+1)*signedSine (j+1) k)|
        ≤ ∑ j ∈ Finset.range 20,
          |coefficient (j+1)*sin (π*(j+1)*k/256)-
            coefficient (j+1)*signedSine (j+1) k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range 20, |coefficient (j+1)| * (1/10000000) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [←mul_sub,abs_mul]
      exact mul_le_mul_of_nonneg_left (errors j hj) (abs_nonneg _)
    _ = (3192/256)*(1/10000000) := by
      rw [←Finset.sum_mul,coefficient_abs_sum]

theorem grid_real_bound (k : Fin 257) (hk : k.val≠0)
    (hpi : (piLower : ℝ) ≤ π)
    (errors : ∀ j ∈ Finset.range 20,
      |sin (π*(j+1)*k.val/256)-signedSine (j+1) k.val| ≤ 1/10000000) :
    |trigNumerator (k.val/128)/(π*k.val/128)| ≤
      (sampleBound k.val : ℝ)/1000000 := by
  have hkn : 0<k.val := Nat.pos_of_ne_zero hk
  have hkreal : (0:ℝ)<k.val := by exact_mod_cast hkn
  have hpilo : (3:ℝ)<piLower := by norm_num [piLower]
  have hpi3 : (3:ℝ)<π := hpilo.trans_le hpi
  have hd0 : 0<3*(k.val:ℝ)/128 := by positivity
  have hdl : 0<(piLower:ℝ)*k.val/128 := by positivity
  have hdp : 0<π*k.val/128 := by positivity
  have hdenl : (piLower:ℝ)*k.val/128 ≤ π*k.val/128 := by gcongr
  have hden3 : 3*(k.val:ℝ)/128 ≤ π*k.val/128 := by gcongr
  have herr := numerator_error k.val errors
  have hnum : |trigNumerator (k.val/128)| ≤
      |(approximateNumerator k.val : ℝ)| + (3192/256)*(1/10000000) := by
    calc
      |trigNumerator (k.val/128)| =
          |(trigNumerator (k.val/128)-(approximateNumerator k.val : ℝ)) +
            (approximateNumerator k.val : ℝ)| := by congr 1; ring
      _ ≤ |trigNumerator (k.val/128)-(approximateNumerator k.val : ℝ)| +
          |(approximateNumerator k.val : ℝ)| := abs_add_le _ _
      _ ≤ (3192/256)*(1/10000000) + |(approximateNumerator k.val : ℝ)| :=
        by linarith
      _ = _ := by ring
  have hq := arithmetic_grid_certificate k hk
  have hreal : (absoluteAccumulator k.val : ℝ)*10000000 + 532*(2*3141592653) ≤
      (sampleBound k.val : ℝ)*(2*3141592653)*10*k.val := by exact_mod_cast hq
  have hcast : |(approximateNumerator k.val : ℝ)| / ((piLower:ℝ)*k.val/128) +
      ((3192/256)*(1/10000000))/(3*k.val/128) ≤
        (sampleBound k.val : ℝ)/1000000 := by
    have hform : |(approximateNumerator k.val : ℝ)| / ((piLower:ℝ)*k.val/128) +
        ((3192/256)*(1/10000000))/(3*k.val/128) =
        ((absoluteAccumulator k.val : ℝ)*10000000+532*(2*3141592653)) /
          ((2*3141592653)*10000000*k.val) := by
      rw [approximateNumerator_abs]
      norm_num [piLower]
      field_simp
      <;> ring
    rw [hform]
    apply (div_le_div_iff₀ (by positivity : (0:ℝ)<(2*3141592653)*10000000*k.val)
      (by norm_num : (0:ℝ)<1000000)).mpr
    nlinarith
  rw [abs_div,abs_of_pos hdp]
  calc
    |trigNumerator (k.val/128)|/(π*k.val/128)
        ≤ (|(approximateNumerator k.val : ℝ)| +
            (3192/256)*(1/10000000))/(π*k.val/128) :=
          div_le_div_of_nonneg_right hnum hdp.le
    _ = |(approximateNumerator k.val : ℝ)|/(π*k.val/128) +
          ((3192/256)*(1/10000000))/(π*k.val/128) := add_div _ _ _
    _ ≤ |(approximateNumerator k.val : ℝ)|/((piLower:ℝ)*k.val/128) +
          ((3192/256)*(1/10000000))/(3*k.val/128) := by
      apply add_le_add
      · exact div_le_div_of_nonneg_left (abs_nonneg _) hdl hdenl
      · exact div_le_div_of_nonneg_left (by positivity) hd0 hden3
    _ ≤ (sampleBound k.val : ℝ)/1000000 := hcast

#print axioms approximateNumerator_identity
#print axioms numerator_error
#print axioms grid_real_bound
end
end RH080PV.Grid
