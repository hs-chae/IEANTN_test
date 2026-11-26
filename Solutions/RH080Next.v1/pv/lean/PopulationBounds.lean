/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import PopulationModel
import SineBridge
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace RH080Next.PopulationPV.Model
open Real
noncomputable section

def approxCos (j k : Nat) : ℝ :=
  if (folded j k).2 then -(sineFixed (folded j k).1 : ℝ)/1000000000
  else (sineFixed (folded j k).1 : ℝ)/1000000000

def signedSplit (j k : Nat) : ℝ :=
  if (folded j k).2 then -(splitProduct (coefficient j) (sineFixed (folded j k).1) : ℝ)
  else (splitProduct (coefficient j) (sineFixed (folded j k).1) : ℝ)

/-- Exact quotient/remainder reasoning for the actual overflow-avoiding split
multiplication. It loses less than one integer unit. -/
theorem splitProduct_error (a s : Nat) :
    |(a : ℝ)*s/1000000000-(splitProduct a s : ℝ)| ≤ 1 := by
  have ha : (a : ℝ) = 1000000000*(a/1000000000 : Nat)+(a%1000000000 : Nat) := by
    exact_mod_cast (Nat.div_add_mod a 1000000000).symm
  have hb : ((a%1000000000*s : Nat) : ℝ) =
      1000000000*((a%1000000000*s)/1000000000 : Nat)+
        ((a%1000000000*s)%1000000000 : Nat) := by
    exact_mod_cast (Nat.div_add_mod (a%1000000000*s) 1000000000).symm
  have hr : (((a%1000000000*s)%1000000000 : Nat) : ℝ) < 1000000000 := by
    exact_mod_cast (Nat.mod_lt (a%1000000000*s) (by decide : 0<1000000000))
  have hr0 : (0 : ℝ) ≤ ((a%1000000000*s)%1000000000 : Nat) := by positivity
  unfold splitProduct
  push_cast
  push_cast at hb
  apply abs_le.mpr
  constructor <;> nlinarith [ha,hb]

theorem cosine_error (j k : Nat) :
    |cos (2*π*j*((k : ℝ)/256))-approxCos j k| ≤ 1/10000000 := by
  let r : Fin 129 := ⟨(folded j k).1, by
    have h := RH080.SineBridge.foldAngle_mem (2*j*k+128)
    change (folded j k).1≤128 at h
    omega⟩
  have accuracy := RH080.SineBridge.sine_fixed_real_error r
  have foldedSin := RH080.SineBridge.sin_foldAngle (2*j*k+128)
  have he : π*((2*j*k+128 : Nat) : ℝ)/256 =
      2*π*j*((k : ℝ)/256)+π/2 := by push_cast; ring
  rw [he, sin_add_pi_div_two] at foldedSin
  change cos (2*π*j*((k : ℝ)/256)) =
    if (folded j k).2 then -sin (π*((folded j k).1 : ℝ)/256)
    else sin (π*((folded j k).1 : ℝ)/256) at foldedSin
  rcases h : folded j k with ⟨index,flipped⟩
  have reduced : |(sineFixed index : ℝ)/1000000000-sin (π*index/256)| ≤
      1/10000000 := by simpa [r,h,sineFixed] using accuracy
  rw [h] at foldedSin
  cases flipped
  · simp only [Bool.false_eq_true,↓reduceIte] at foldedSin
    rw [foldedSin]
    simpa [approxCos,h,abs_sub_comm] using reduced
  · simp only [↓reduceIte] at foldedSin
    rw [foldedSin]
    convert reduced using 1 <;> simp [approxCos,h] <;> congr 1 <;> ring

theorem signedSplit_error (j k : Nat) :
    |(coefficient j : ℝ)*approxCos j k-signedSplit j k| ≤ 1 := by
  have h := splitProduct_error (coefficient j) (sineFixed (folded j k).1)
  unfold approxCos signedSplit
  split_ifs
  · calc
      _ = |-((coefficient j : ℝ)*(sineFixed (folded j k).1 : ℝ)/1000000000-
          (splitProduct (coefficient j) (sineFixed (folded j k).1) : ℝ))| := by
        congr 1
        ring
      _ = _ := abs_neg _
      _ ≤ 1 := h
  · convert h using 1 <;> congr 1 <;> ring

theorem signedTerm_eq (j k : Nat) :
    signedTerm j k = (weight j : ℝ)*signedSplit j k := by
  unfold signedTerm signedSplit
  split <;> simp only [Nat.cast_mul, mul_neg]

theorem pointStep_difference (k j : Nat) (state : Nat×Nat) :
    ((pointStep k state j).1 : ℝ)-((pointStep k state j).2 : ℝ) =
      (state.1 : ℝ)-(state.2 : ℝ)+signedTerm j k := by
  unfold pointStep signedTerm
  split <;> push_cast <;> ring

theorem rawSample_difference (k : Nat) :
    ((rawSample k).1 : ℝ)-((rawSample k).2 : ℝ) =
      ∑ j ∈ Finset.range 16, signedTerm j k := by
  have h (n : Nat) :
      (((List.range n).foldl (pointStep k) (0,0)).1 : ℝ)-
      (((List.range n).foldl (pointStep k) (0,0)).2 : ℝ) =
      ∑ j ∈ Finset.range n, signedTerm j k := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil, Finset.sum_range_succ]
      rw [pointStep_difference, ih]
  exact h 16

#print axioms splitProduct_error
#print axioms cosine_error
#print axioms signedSplit_error
#print axioms rawSample_difference
end
end RH080Next.PopulationPV.Model
