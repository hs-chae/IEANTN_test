/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ForwardRamanujan.Old
namespace ForwardRamanujan.KernelSource
open FKS2Table4 SumStability
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
/-- Direct kernel reduction of the full actual source match; no native fact. -/
theorem source_guard : sourceMatches Old.actualSource Old.program=true := by decide +kernel

/-- Reconstruct the same execution using the kernel source certificate. -/
theorem execution : Exec Old.actualSource Old.program Old.initial Old.out := by
  obtain ⟨final,hkernel⟩ := ForwardRamanujan.kernel_from_chain Old.execution_check.2.2.2.1
    (show Old.data.length≤64 by rw [Old.enclosure_check.1];norm_num)
  exact ⟨source_guard,by decide,by decide,Old.data,Old.sumOut,final,Old.execution_check.1,
    Old.execution_check.2.1,Old.execution_check.2.2.1,hkernel,Old.execution_check.2.2.2.2.1,Old.suffix_IEEE⟩

theorem certified_upper : upper (Old.m:ℝ) (Old.M:ℝ) (Old.A:ℝ) (Old.Y:ℝ)≤(Old.bound:ℝ) := by
  rw [Old.upper_as_targets]
  have h := Old.verified_with_domain Old.checked_domain execution
  have hb : (Old.out:ℝ)+(Old.totalError:ℝ)≤(Old.bound:ℝ) := by
    exact_mod_cast Old.budget_check.2.2.2.2.2.2
  exact h.trans hb
end ForwardRamanujan.KernelSource
