/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FKS2Update.Source

namespace FKS2Update
open FKS2Scalar FKS2Correction

def updatedError : ℚ := transportDelta+coefficientRatio*totalError

theorem target_parameter_transport :
    FKS2Numerics.v3.nuStar 0.0000000001 300 =
      (coefficientRatio:ℝ)*FKS2Numerics.v3.nuStar 121.096 300 := by
  unfold FKS2Numerics.v3.nuStar FKS2.v2.nuAsymp coefficientRatio
  push_cast
  ring

theorem updated_budget_checks :
    0 < coefficientRatio ∧ 0 ≤ updatedError ∧
    updatedError ≤ 1/10^56 ∧ updatedQ+updatedError ≤ (2:ℚ)/10^49 := by
  native_decide

theorem updated_whole_error :
    |(updatedQ:ℝ)-FKS2Numerics.v3.nuStar 0.0000000001 300| ≤ (updatedError:ℝ) := by
  have hratio : (0:ℝ) < (coefficientRatio:ℝ) := by
    exact_mod_cast updated_budget_checks.1
  have hd : |(updatedQ:ℝ)-(coefficientRatio:ℝ)*(baselineQ:ℝ)| ≤ (transportDelta:ℝ) := by
    exact_mod_cast output_transport_check
  have hs : |(coefficientRatio:ℝ)*(baselineQ:ℝ)-
      (coefficientRatio:ℝ)*FKS2Numerics.v3.nuStar 121.096 300| ≤
      (coefficientRatio:ℝ)*(totalError:ℝ) := by
    rw [← mul_sub,abs_mul,abs_of_pos hratio]
    exact mul_le_mul_of_nonneg_left
      (baseline_source_error baseline_source_execution) hratio.le
  rw [target_parameter_transport]
  calc
    _ ≤ |(updatedQ:ℝ)-(coefficientRatio:ℝ)*(baselineQ:ℝ)| +
        |(coefficientRatio:ℝ)*(baselineQ:ℝ)-
          (coefficientRatio:ℝ)*FKS2Numerics.v3.nuStar 121.096 300| := abs_sub_le _ _ _
    _ ≤ (transportDelta:ℝ)+(coefficientRatio:ℝ)*(totalError:ℝ) := add_le_add hd hs
    _ = _ := by simp [updatedError]

theorem updated_source_error {out : ℚ} (h : ExecC updatedProgram out) :
    |(out:ℝ)-FKS2Numerics.v3.nuStar 0.0000000001 300| ≤ (updatedError:ℝ) := by
  have ho : out = updatedQ := Option.some.inj (h.symm.trans updated_source_execution)
  rw [ho]
  exact updated_whole_error

theorem updated_error_witness :
    ∃ out : ℚ, ExecC updatedProgram out ∧
      |(out:ℝ)-FKS2Numerics.v3.nuStar 0.0000000001 300| ≤ (updatedError:ℝ) := by
  exact ⟨updatedQ,updated_source_execution,updated_source_error updated_source_execution⟩

theorem updated_provider : FKS2Numerics.v4.updated_bound := by
  have h := (abs_le.mp (updated_source_error updated_source_execution)).1
  have hb : (updatedQ:ℝ)+(updatedError:ℝ) ≤ (2:ℝ)/10^49 := by
    simpa only [Rat.cast_add,Rat.cast_div,Rat.cast_ofNat,Rat.cast_pow]
      using (Rat.cast_le (K := ℝ)).2 updated_budget_checks.2.2.2
  unfold FKS2Numerics.v4.updated_bound
  linarith

end FKS2Update
