/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTPairedIntModel
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
namespace RH080Next.FFT.IntegerModel

theorem le_ceilDiv_mul (a b : Nat) (hb : 0<b) : a≤ceilDiv a b*b := by
  unfold ceilDiv
  split_ifs with h
  · simpa [h, Nat.mul_comm] using (Nat.div_add_mod a b).symm.le
  · have hm := Nat.mod_lt a hb
    have hd := Nat.div_add_mod a b
    nlinarith

theorem real_div_le_ceilDiv (a b : Nat) (hb : 0<b) :
    (a:ℝ)/(b:ℝ)≤(ceilDiv a b:ℝ) := by
  apply (div_le_iff₀ (by exact_mod_cast hb : (0:ℝ)<b)).mpr
  exact_mod_cast le_ceilDiv_mul a b hb

theorem three_ceil_lower (a b c d : Nat) (hb : 0<b) (hc : 0<c) (hd : 0<d) :
    (a:ℝ)/(b:ℝ)/(c:ℝ)/(d:ℝ)≤(ceilDiv (ceilDiv (ceilDiv a b) c) d:ℝ) := by
  have h₁ := real_div_le_ceilDiv a b hb
  have h₂ := (div_le_div_of_nonneg_right h₁ (by positivity : (0:ℝ)≤c)).trans
    (real_div_le_ceilDiv (ceilDiv a b) c hc)
  exact (div_le_div_of_nonneg_right h₂ (by positivity : (0:ℝ)≤d)).trans
    (real_div_le_ceilDiv (ceilDiv (ceilDiv a b) c) d hd)

/-- The actual w4 final three upward divisions, curvature allowance and
100 ulps dominate the exact average plus true FFT error. Pure arithmetic;
source execution and the input-dependent integral remain separate proofs. -/
theorem w4_upward_budget (total quad n : Nat) (hn : 0<n) :
    (total:ℝ)/((unit:ℝ)*n)+(quad:ℝ)/(3*10000000000000000*(n:ℝ)^2)+
      1/100000000000000 ≤
    ((ceilDiv (ceilDiv (ceilDiv total 1000000000000000000) 100) n+
      ceilDiv (ceilDiv (ceilDiv quad 3) n) n+100:Nat):ℝ)/10000000000000000 := by
  have hfirst := div_le_div_of_nonneg_right
    (three_ceil_lower total 1000000000000000000 100 n (by norm_num) (by norm_num) hn)
    (by norm_num : (0:ℝ)≤10000000000000000)
  have hsecond := div_le_div_of_nonneg_right
    (three_ceil_lower quad 3 n n (by norm_num) hn hn)
    (by norm_num : (0:ℝ)≤10000000000000000)
  have hh := add_le_add hfirst hsecond
  have hunit : (unit:ℝ)=1000000000000000000000000000000000000 := by norm_num [unit]
  rw [hunit]
  push_cast
  have hnr : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  convert add_le_add_right hh (1/100000000000000:ℝ) using 1
  all_goals first | rfl | (norm_num; ring) | (field_simp [hnr] <;> ring)

#print axioms le_ceilDiv_mul
#print axioms three_ceil_lower
#print axioms w4_upward_budget
end RH080Next.FFT.IntegerModel
