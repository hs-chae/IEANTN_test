/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
/- Comparisons of full bound functions only. This does not prove an RH-to-M bound. -/
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic
namespace RHContinuation.MobiusFrontier
open Real Set
noncomputable def scaledCandidate (L:ℝ) : ℝ := 1100000*L^2*Real.exp (-(25/132:ℝ)*L)
lemma scaled_antitone : AntitoneOn scaledCandidate (Ici 132) := by
  have hd (L:ℝ) : HasDerivAt scaledCandidate
      (1100000*Real.exp (-(25/132:ℝ)*L)*(2*L-(25/132:ℝ)*L^2)) L := by
    convert (((hasDerivAt_id L).pow 2).const_mul 1100000).mul
      (((hasDerivAt_id L).const_mul (-(25/132:ℝ))).exp) using 1 <;> first | rfl | (simp only [id_eq,Pi.pow_apply]; ring)
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici (132:ℝ)) (by unfold scaledCandidate; fun_prop)
    (fun L hL => (hd L).hasDerivWithinAt)
  intro L hL
  simp only [interior_Ici,mem_Ioi] at hL
  have hl0 : 0≤L := by linarith
  have hs : 2*L-(25/132:ℝ)*L^2≤0 := by nlinarith
  exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hs
lemma scaled_at_132 : scaledCandidate 132<0.3 := by
  have he : (64000000000:ℝ)<Real.exp 25 := by
    calc _ < (2.7182818283:ℝ)^25 := by norm_num
      _ < (Real.exp 1)^25 := by gcongr; exact Real.exp_one_gt_d9
      _ = Real.exp 25 := by rw [← Real.exp_nat_mul]; norm_num
  unfold scaledCandidate
  norm_num
  rw [Real.exp_neg]
  rw [← div_eq_mul_inv]
  change (19166400000:ℝ)/Real.exp 25<(3/10:ℝ)
  exact (div_lt_iff₀ (Real.exp_pos _)).mpr (by linarith)
/-- Strict improvement over the full RZA Theorem1.1 function, not its rounded abstract. -/
theorem below_RZA_full {L:ℝ} (hL:132≤L) :
    1100000*Real.exp (-(25/132:ℝ)*L)<(0.006688*L-0.039)/L^2 := by
  have hm := scaled_antitone (show (132:ℝ)∈Ici 132 by simp) hL hL
  have hb : scaledCandidate L<0.3 := hm.trans_lt scaled_at_132
  apply (lt_div_iff₀ (by positivity : 0<L^2)).mpr
  unfold scaledCandidate at hb
  nlinarith
lemma scaled_at_200 : scaledCandidate 200<0.01 := by
  have he : (10000000000000:ℝ)<Real.exp 37 := by
    calc _ < (2.7182818283:ℝ)^37 := by norm_num
      _ < (Real.exp 1)^37 := by gcongr; exact Real.exp_one_gt_d9
      _ = Real.exp 37 := by rw [← Real.exp_nat_mul]; norm_num
  have he' : (10000000000000:ℝ)<Real.exp ((25/132:ℝ)*200) :=
    he.trans (Real.exp_lt_exp.mpr (by norm_num))
  unfold scaledCandidate
  rw [show -(25/132:ℝ)*200 = -((25/132:ℝ)*200) by ring,Real.exp_neg]
  rw [← div_eq_mul_inv]
  norm_num only [show (1100000:ℝ)*200^2=44000000000 by norm_num]
  exact (div_lt_iff₀ (Real.exp_pos _)).mpr (by linarith)
/-- The actual JLT headline function, TheoremA.1(A.5), all x>1. -/
theorem below_JLT_headline {L:ℝ} (hL:200≤L) :
    1100000*Real.exp (-(25/132:ℝ)*L)<2.9189/L^2 := by
  have hm := scaled_antitone (show (200:ℝ)∈Ici 132 by norm_num) (by change 132≤L; linarith) hL
  have hb : scaledCandidate L<0.01 := hm.trans_lt scaled_at_200
  apply (lt_div_iff₀ (by positivity : 0<L^2)).mpr
  unfold scaledCandidate at hb
  linarith
#print axioms below_RZA_full
#print axioms below_JLT_headline
end RHContinuation.MobiusFrontier
