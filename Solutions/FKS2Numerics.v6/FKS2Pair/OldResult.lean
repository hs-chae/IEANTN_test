/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FKS2Pair.OldInputs

namespace FKS2Pair.Old
open Real IEANTN FKS2Scalar FKS2Table4 SumStability

def anchorHi : ℚ := (330/300)*(expHi (-15))^2*(1.6997e-12+oldU 0)
def scaledOutput : ℚ := (round64 (sumOut*scale)).getD 0
def anchorOutput : ℚ := (round64 (scaledOutput+anchorUpper)).getD 0
def pointOutput : ℚ := (round64 (anchorOutput+pointUpper)).getD 0
def suffixError : ℚ := 4/10^27
def totalError : ℚ := forwardError scale sumOut suffixError

theorem boundary_checks :
    scale=1/(2:ℚ)^48 ∧ anchorHi ≤ anchorUpper ∧ oldU 30 ≤ pointUpper ∧
    oldU 30/328 ≤ tailUpper ∧ 0 ≤ scale ∧ (data.map abs).sum=data.sum ∧
    data.sum=∑ j ∈ Finset.range 30,data[j]! := by native_decide

theorem suffix_checks :
    scaledOutput=scale*sumOut ∧
    round64 (scaledOutput+anchorUpper)=some anchorOutput ∧
    round64 (anchorOutput+pointUpper)=some pointOutput ∧
    round64 (pointOutput+tailUpper)=some out ∧
    additionCheck (scaledOutput+anchorUpper) anchorOutput=true ∧
    additionCheck (anchorOutput+pointUpper) pointOutput=true ∧
    additionCheck (pointOutput+tailUpper) out=true ∧
    |anchorOutput-(scaledOutput+anchorUpper)| ≤ 1/10^27 ∧
    |pointOutput-(anchorOutput+pointUpper)| ≤ 1/10^27 ∧
    |out-(pointOutput+tailUpper)| ≤ 1/10^27 := by native_decide

theorem literal_scale_check :
    loadLiteral oldProgram.scale=some scale ∧ loadLiteral oldProgram.anchor=some anchorUpper ∧
    loadLiteral oldProgram.point=some pointUpper ∧ loadLiteral oldProgram.tail=some tailUpper ∧
    additionCheck (sumOut*scale) scaledOutput=true := by native_decide

theorem suffix_IEEE : SuffixIEEE oldProgram sumOut out := by
  exact ⟨scale,anchorUpper,pointUpper,tailUpper,scaledOutput,anchorOutput,pointOutput,
    literal_scale_check.1,literal_scale_check.2.1,literal_scale_check.2.2.1,
    literal_scale_check.2.2.2.1,additionCheck_sound literal_scale_check.2.2.2.2,
    additionCheck_sound suffix_checks.2.2.2.2.1,
    additionCheck_sound suffix_checks.2.2.2.2.2.1,
    additionCheck_sound suffix_checks.2.2.2.2.2.2.1⟩

theorem concrete_execution : ExecTransportAt oldSource oldProgram st out := by
  obtain ⟨final,hkernel⟩ := kernel_execution
  exact ⟨source_checked,by decide,data,sumOut,final,execution_checks.1,
    execution_checks.2.1,execution_checks.2.2.1,hkernel,execution_checks.2.2.2.2,suffix_IEEE⟩

theorem suffix_roundoff :
    |out-(scale*sumOut+anchorUpper+pointUpper+tailUpper)| ≤ suffixError := by
  have h1 := abs_le.mp suffix_checks.2.2.2.2.2.2.2.1
  have h2 := abs_le.mp suffix_checks.2.2.2.2.2.2.2.2.1
  have h3 := abs_le.mp suffix_checks.2.2.2.2.2.2.2.2.2
  rw [suffix_checks.1] at h1
  rw [abs_le]
  unfold suffixError
  constructor <;> linarith

theorem scaled_cells_upper : cells profile ≤ (scale:ℝ)*(data.sum:ℚ) := by
  rw [boundary_checks.2.2.2.2.2.2,Rat.cast_sum,Finset.mul_sum]
  unfold cells
  apply Finset.sum_le_sum
  intro j hj
  have h := scaled_cell j hj
  simpa only [profile,boundary_checks.1,Rat.cast_div,Rat.cast_one,Rat.cast_pow,Rat.cast_ofNat] using h

theorem anchor_upper : anchor profile ≤ (anchorUpper:ℝ) := by
  have he := exp_pow_upper (n := 2) (by
    simpa [arg] using exp_checks.2 0 (by decide : 0 ∈ Finset.range 30))
  have hexp : exp (-30:ℝ) ≤ ((expHi (-15))^2:ℚ) := by norm_num at he ⊢;exact he
  simp only [Rat.cast_pow] at hexp
  have hbound : anchor profile ≤ (anchorHi:ℝ) := by
    unfold anchor profile anchorHi
    push_cast
    have hu : (0:ℝ) ≤ 1.6997e-12+(oldU 0:ℝ) := by norm_num [oldU]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hexp (by norm_num : (0:ℝ)≤330/300)) hu
  exact hbound.trans (by exact_mod_cast boundary_checks.2.1)

theorem point_upper : profile 30 ≤ (pointUpper:ℝ) := by
  unfold profile
  exact_mod_cast boundary_checks.2.2.1
theorem tail_upper : profile 30/328 ≤ (tailUpper:ℝ) := by
  unfold profile
  exact_mod_cast boundary_checks.2.2.2.1

theorem budget_checks :
    0 ≤ totalError ∧ totalError ≤ 1/10^26 ∧ out+totalError < (1.69e-12:ℚ) := by
  native_decide

/-- Arbitrary outputs of the actual old source, not an exact-sum target certificate. -/
theorem verified_old_transport {q : ℚ} (he : ExecTransportAt oldSource oldProgram st q) :
    Bsafe profile ≤ (q:ℝ)+(totalError:ℝ) := by
  have hd : ValidInputs data := by
    intro r hr
    exact FKS2SumBridge.inputCheck_sound (enclosure_checks.2.1 r hr)
  have hf : |(out:ℝ)-((scale:ℝ)*(sumOut:ℝ)+(anchorUpper:ℝ)+
      (pointUpper:ℝ)+(tailUpper:ℝ))| ≤ (suffixError:ℝ) := by exact_mod_cast suffix_roundoff
  exact source_linked_transport_upper he execution_checks.1 execution_checks.2.2.1
    execution_checks.2.2.2.2 enclosure_checks.1 hd boundary_checks.2.2.2.2.2.1
    boundary_checks.2.2.2.2.1 scaled_cells_upper anchor_upper point_upper tail_upper hf

theorem selected_execution_witness : ∃ q : ℚ,
    ExecTransportAt oldSource oldProgram st q ∧ Bsafe profile ≤ (q:ℝ)+(totalError:ℝ) :=
  ⟨out,concrete_execution,verified_old_transport concrete_execution⟩

theorem certified_allowance : Bsafe profile < (1.69e-12:ℝ) := by
  have h : (out:ℝ)+(totalError:ℝ)<(1.69e-12:ℝ) := by
    have hc := (Rat.cast_lt (K := ℝ)).2 budget_checks.2.2
    push_cast at hc
    convert hc using 1
  exact (verified_old_transport concrete_execution).trans_lt h

theorem profile_valid
    (h300 : ∀ t ≥ exp 300,Eθ t ≤ 1.6930e-12)
    (h310 : ∀ t ≥ exp 310,Eθ t ≤ 1.6882e-12)
    (h320 : ∀ t ≥ exp 320,Eθ t ≤ 1.6837e-12)
    (h330 : ∀ t ≥ exp 330,Eθ t ≤ 1.6795e-12) : ValidProfile profile := by
  constructor
  · intro j hj
    unfold profile
    exact_mod_cast oldU_nonneg j
  · intro j hj t ht
    unfold profile oldU
    split_ifs with h10 h20 h30
    · exact h300 t ((exp_le_exp.mpr (by linarith [(Nat.cast_nonneg j : (0:ℝ)≤j)] : (300:ℝ) ≤ 300+(j:ℝ))).trans ht)
    · have hjge : (10:ℝ)≤j := by exact_mod_cast (show 10≤j by omega)
      exact h310 t ((exp_le_exp.mpr (by linarith : (310:ℝ) ≤ 300+(j:ℝ))).trans ht)
    · have hjge : (20:ℝ)≤j := by exact_mod_cast (show 20≤j by omega)
      exact h320 t ((exp_le_exp.mpr (by linarith : (320:ℝ) ≤ 300+(j:ℝ))).trans ht)
    · have he : j=30 := by omega
      subst j
      exact h330 t (by norm_num at ht;exact ht)

/-- Four genuine old Table3 whole-tail premises and the independent shared anchor. -/
theorem numerical_pi
    (h300 : ∀ t ≥ exp 300,Eθ t ≤ 1.6930e-12)
    (h310 : ∀ t ≥ exp 310,Eθ t ≤ 1.6882e-12)
    (h320 : ∀ t ≥ exp 320,Eθ t ≤ 1.6837e-12)
    (h330 : ∀ t ≥ exp 330,Eθ t ≤ 1.6795e-12)
    (hAnchor : Eπ (exp 300) ≤ 1.6997e-12) :
    HasNumericalBound Eπ (1.69e-12:ℝ) (exp 330) := by
  intro x hx
  exact (FKS2Pair.whole_ray_transport (profile_valid h300 h310 h320 h330) hAnchor x hx).trans
    certified_allowance.le
end FKS2Pair.Old
