/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import PVEvolutionA.Result
import ScopedWinnerA.Coverage
import PVEvolutionA.Cumulative
namespace PVEvolutionA
open Real IEANTN WinnerDirectKernel
set_option maxHeartbeats 0
noncomputable def scopedExact : ℝ :=
  (1+1/1000000000)*(9471452/1000000000)+1/1000000000000+1/100000000

theorem coefficient_order : Cmid ≤ C330 ∧ C330 ≤ C300 ∧ C300<scopedExact ∧
    scopedExact<ScopedWinnerA.Comparison.oldExact := by
  norm_num [Cmid,C330,C300,scopedExact,ScopedWinnerA.Comparison.oldExact]

theorem bound_below_300 {x:ℝ} (hx:exp (300:ℝ) ≤ x) : bound x ≤ C300*scale x := by
  have hscale : 0 ≤ scale x := rpow_nonneg ((exp_pos _).trans_le hx).le _
  unfold bound
  split_ifs
  · exact mul_le_mul_of_nonneg_right (coefficient_order.1.trans coefficient_order.2.1) hscale
  · exact mul_le_mul_of_nonneg_right coefficient_order.2.1 hscale
  · exact le_rfl

theorem whole_ray_increment {x:ℝ} (hx:exp (300:ℝ) ≤ x) :
    bound x+(317/100000000:ℝ)*scale x<scopedExact*scale x := by
  apply (add_le_add (bound_below_300 hx) le_rfl).trans_lt
  rw [←add_mul]
  apply mul_lt_mul_of_pos_right _ (rpow_pos_of_pos ((exp_pos _).trans_le hx) _)
  norm_num [C300,scopedExact]

theorem domain_nonempty : ScopedWinnerA.Comparison.domain (exp (330:ℝ)) :=
  ⟨le_rfl,exp_le_exp.mpr (by norm_num)⟩
theorem margin_positive {x:ℝ} (hx:ScopedWinnerA.Comparison.domain x) :
    0<(32094/100000000:ℝ)*scale x :=
  mul_pos (by norm_num) (rpow_pos_of_pos ((exp_pos _).trans_le hx.1) _)

theorem bound_comparison {x:ℝ} (hx:ScopedWinnerA.Comparison.domain x) :
    bound x ≤ C330*scale x := by
  unfold bound
  split_ifs with hm hd
  · exact mul_le_mul_of_nonneg_right (by norm_num [Cmid,C330]) (rpow_nonneg ((exp_pos _).trans_le hx.1).le _)
  · exact le_rfl
  · exact (hd hx.1).elim

theorem strict_scoped {x:ℝ} (hx:ScopedWinnerA.Comparison.domain x) :
    bound x+(32094/100000000:ℝ)*scale x<scopedExact*scale x := by
  apply (add_le_add (bound_comparison hx) le_rfl).trans_lt
  rw [←add_mul]
  apply mul_lt_mul_of_pos_right _ (rpow_pos_of_pos ((exp_pos _).trans_le hx.1) _)
  norm_num [C330,scopedExact]

theorem strict_old39 {x:ℝ} (hx:ScopedWinnerA.Comparison.domain x) :
    bound x+(32393/100000000:ℝ)*scale x<ScopedWinnerA.Coverage.envelope x := by
  rw [ScopedWinnerA.Coverage.envelope_exact hx]
  apply (add_le_add (bound_comparison hx) le_rfl).trans_lt
  change C330*scale x+_<_*scale x
  rw [←add_mul]
  apply mul_lt_mul_of_pos_right _ (rpow_pos_of_pos ((exp_pos _).trans_le hx.1) _)
  norm_num [C330,ScopedWinnerA.Comparison.oldExact]

section OriginalInputs
variable
    (hCHJ : OriginalCHJSource)
    (hrvm : ZeroCount.v1.rvm_error_bound) (hsmall : ZeroCount.v1.rvm_error_small)
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    (h : WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH : RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH : ZetaZeroFreeHalfPlane (7/8))
include hCHJ hrvm hsmall hlow h hRH hQRH
/-- Both old and new actual-prime theorems are consumed; every written old
identity remains represented. The no-PV challenger is not fabricated. -/
theorem snapshot_evolution {x:ℝ} (hx:ScopedWinnerA.Comparison.domain x) :
    Eπ x ≤ bound x ∧ Eπ x ≤ scopedExact*scale x ∧ Eπ x ≤ ScopedWinnerA.Coverage.envelope x ∧
    bound x+(32094/100000000:ℝ)*scale x<scopedExact*scale x ∧
    bound x+(32393/100000000:ℝ)*scale x<ScopedWinnerA.Coverage.envelope x ∧
    (∀ i:Fin 39,Eπ x ≤ ScopedWinnerA.Coverage.allowance x i) := by
  have hp:=pi_evolved hCHJ hrvm hsmall hlow h hRH hQRH
    ((exp_le_exp.mpr (by norm_num : (300:ℝ) ≤ 330)).trans hx.1)
  have ho:=ScopedWinnerA.incumbent_valid hCHJ hrvm hsmall hlow h hRH hQRH hx
  have he:=ScopedWinnerA.Coverage.envelope_exact hx
  have heold:=ScopedWinnerA.Comparison.old_envelope_exact hx
  have ho' : Eπ x ≤ ScopedWinnerA.Coverage.envelope x := by rwa [he,←heold]
  have hs0:=ScopedWinnerA.pi_refined_exact hCHJ hrvm hsmall hlow h hRH hQRH x
    ((exp_le_exp.mpr (by norm_num : (300:ℝ) ≤ 330)).trans hx.1)
  have hs : Eπ x ≤ scopedExact*scale x := by
    simpa only [scopedExact,scale,pow_zero,mul_one,show (7/8:ℝ)-1= -(1:ℝ)/8 by norm_num] using hs0
  exact ⟨hp,hs,ho',strict_scoped hx,strict_old39 hx,fun i=>ho'.trans
    (Finset.inf'_le (ScopedWinnerA.Coverage.allowance x) (Finset.mem_univ i))⟩
end OriginalInputs
#print axioms snapshot_evolution
#print axioms strict_scoped
end PVEvolutionA
