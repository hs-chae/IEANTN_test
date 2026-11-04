/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import OriginalRightMoment
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.NumberTheory.LSeries.RiemannZeta
namespace WinnerOriginalScalars
open Real Set MeasureTheory
set_option maxHeartbeats 0
noncomputable def positiveZeta (s : ℝ) : ℝ := ∑' n : ℕ, ((n:ℝ)+1)^(-s)

theorem positiveZeta_summable {s : ℝ} (hs : 1<s) :
    Summable (fun n : ℕ => ((n:ℝ)+1)^(-s)) := by
  have h := (summable_nat_rpow.mpr (by linarith : -s < -1)).comp_injective Nat.succ_injective
  simpa [Function.comp_def,Nat.cast_succ] using h

theorem positiveZeta_lower {s : ℝ} (hs : 1<s) : 1≤positiveZeta s := by
  have h := (positiveZeta_summable hs).le_tsum 0 (fun n _ => rpow_nonneg (by positivity) _)
  simpa [positiveZeta] using h

theorem positiveZeta_upper {s : ℝ} (hs : 1<s) : positiveZeta s≤1+1/(s-1) := by
  have hanti : AntitoneOn (fun x : ℝ => x^(-s)) (Ici (1:ℝ)) := by
    intro x hx y hy hxy
    exact rpow_le_rpow_of_nonpos (by linarith [show 1≤x from hx]) hxy (by linarith)
  have hi := integrableOn_Ioi_rpow_of_lt (by linarith : -s < -1) (by norm_num : (0:ℝ)<1)
  have ht := AntitoneOn.tsum_comp_add_le_integral (f:=fun x : ℝ => x^(-s)) 1 (by simpa using hanti) (by simpa using hi) (fun t ht => rpow_nonneg (by norm_num at ht; linarith) _)
  norm_num only [Nat.cast_one] at ht
  rw [integral_Ioi_rpow_of_lt (by linarith : -s < -1) (by norm_num : (0:ℝ)<1)] at ht
  have hz := (positiveZeta_summable hs).tsum_eq_zero_add
  simp only [Nat.cast_zero,zero_add,one_rpow,Nat.cast_add,Nat.cast_one] at hz
  have he : (∑' n : ℕ, ((n:ℝ)+1+1)^(-s)) = ∑' n : ℕ, ((n:ℝ)+1+1)^(-s) := rfl
  simp only [Nat.cast_add,Nat.cast_one,one_rpow] at ht
  unfold positiveZeta
  rw [hz]
  have hr : (-1:ℝ)/(-s+1)=1/(s-1) := by
    field_simp [show -s+1≠0 by linarith,show s-1≠0 by linarith]
    <;> ring
  rw [hr] at ht
  linarith

theorem positiveZeta_complex {s : ℝ} (hs : 1<s) :
    (positiveZeta s:ℂ)=riemannZeta (s:ℂ) := by
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by simpa using hs)]
  rw [positiveZeta,Complex.ofReal_tsum]
  apply tsum_congr
  intro n
  rw [←Complex.ofReal_natCast,←Complex.ofReal_one,←Complex.ofReal_add,
    ←Complex.ofReal_cpow (by positivity : (0:ℝ)≤(n:ℝ)+1)]
  rw [←Complex.ofReal_div]
  congr 1
  rw [rpow_neg (by positivity),one_div]

 theorem zeta_eta_upper : positiveZeta (1+(507/2000:ℝ))≤5 := by
  have h := positiveZeta_upper (s:=1+(507/2000)) (by norm_num)
  norm_num at h ⊢
  linarith

 theorem zeta_two_eta_lower : 1≤positiveZeta (2+2*(507/2000:ℝ)) :=
  positiveZeta_lower (by norm_num)

#print axioms zeta_eta_upper
#print axioms positiveZeta_complex
end WinnerOriginalScalars
