/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import CertData.DensityPointRow192
import Mathlib.Tactic.IntervalCases
import CertData.DensityBlockRow192_00
import CertData.DensityBlockRow192_01
import CertData.DensityBlockRow192_02
import CertData.DensityBlockRow192_03
import CertData.DensityBlockRow192_04
import CertData.DensityBlockRow192_05
import CertData.DensityBlockRow192_06
import CertData.DensityBlockRow192_07
import CertData.DensityBlockRow192_08
import CertData.DensityBlockRow192_09
import CertData.DensityBlockRow192_10
import CertData.DensityBlockRow192_11
import CertData.DensityBlockRow192_12
import CertData.DensityBlockRow192_13
import CertData.DensityBlockRow192_14
import CertData.DensityBlockRow192_15
import CertData.DensityBlockRow192_16
import CertData.DensityBlockRow192_17
import CertData.DensityBlockRow192_18
import CertData.DensityBlockRow192_19
import CertData.DensityBlockRow192_20
import CertData.DensityBlockRow192_21
import CertData.DensityBlockRow192_22
import CertData.DensityBlockRow192_23
import CertData.DensityBlockRow192_24
import CertData.DensityBlockRow192_25
import CertData.DensityBlockRow192_26
import CertData.DensityBlockRow192_27
import CertData.DensityBlockRow192_28
import CertData.DensityBlockRow192_29
import CertData.DensityBlockRow192_30
import CertData.DensityBlockRow192_31
set_option maxRecDepth 10000
open DensityNumeric
namespace DensityBlockResultRow192
theorem endpoint_upper : Q (7/8) 61 ≤ (18473 : ℝ) / 2000000 := DensityPointRow192.endpoint_upper
theorem base_upper : Real.exp (-(192:ℝ)/8) *
    (((61:ℝ)+(1:ℝ)/10^9)^2/(2*Real.pi)+(2+1/Real.pi)*((61:ℝ)+(1:ℝ)/10^9)) ≤ (1 : ℝ) / 10000000 := DensityPointRow192.base_upper

private noncomputable def blockBound (b : ℕ) : ℝ :=
  [(16353 : ℝ) / 6250000, (174651 : ℝ) / 100000000, (29157 : ℝ) / 25000000, (15583 : ℝ) / 20000000, (13019 : ℝ) / 25000000, (34823 : ℝ) / 100000000, (23297 : ℝ) / 100000000, (3119 : ℝ) / 20000000, (2089 : ℝ) / 20000000, (7 : ℝ) / 100000, (939 : ℝ) / 20000000, (3151 : ℝ) / 100000000, (2117 : ℝ) / 100000000, (89 : ℝ) / 6250000, (959 : ℝ) / 100000000, (647 : ℝ) / 100000000, (437 : ℝ) / 100000000, (37 : ℝ) / 12500000, (101 : ℝ) / 50000000, (69 : ℝ) / 50000000, (19 : ℝ) / 20000000, (33 : ℝ) / 50000000, (23 : ℝ) / 50000000, (33 : ℝ) / 100000000, (3 : ℝ) / 12500000, (9 : ℝ) / 50000000, (7 : ℝ) / 50000000, (11 : ℝ) / 100000000, (1 : ℝ) / 10000000, (1 : ℝ) / 12500000, (7 : ℝ) / 100000000, (7 : ℝ) / 100000000].getD b 0

theorem sum_upper : (∑ i ∈ Finset.range 512, cellTerm 192 61 i) ≤ (7893399999 : ℝ) / 1000000000000 := by
  rw [sum_512_blocks]
  have h : ∀ b ∈ Finset.range 32,
      (∑ k ∈ Finset.Icc (0 : ℕ) 15, cellTerm 192 61 (b * 16 + k)) ≤ blockBound b := by
    intro b hb
    have hb' : b < 32 := Finset.mem_range.mp hb
    interval_cases b
    · exact DensityBlockRow192.block_00
    · exact DensityBlockRow192.block_01
    · exact DensityBlockRow192.block_02
    · exact DensityBlockRow192.block_03
    · exact DensityBlockRow192.block_04
    · exact DensityBlockRow192.block_05
    · exact DensityBlockRow192.block_06
    · exact DensityBlockRow192.block_07
    · exact DensityBlockRow192.block_08
    · exact DensityBlockRow192.block_09
    · exact DensityBlockRow192.block_10
    · exact DensityBlockRow192.block_11
    · exact DensityBlockRow192.block_12
    · exact DensityBlockRow192.block_13
    · exact DensityBlockRow192.block_14
    · exact DensityBlockRow192.block_15
    · exact DensityBlockRow192.block_16
    · exact DensityBlockRow192.block_17
    · exact DensityBlockRow192.block_18
    · exact DensityBlockRow192.block_19
    · exact DensityBlockRow192.block_20
    · exact DensityBlockRow192.block_21
    · exact DensityBlockRow192.block_22
    · exact DensityBlockRow192.block_23
    · exact DensityBlockRow192.block_24
    · exact DensityBlockRow192.block_25
    · exact DensityBlockRow192.block_26
    · exact DensityBlockRow192.block_27
    · exact DensityBlockRow192.block_28
    · exact DensityBlockRow192.block_29
    · exact DensityBlockRow192.block_30
    · exact DensityBlockRow192.block_31
  apply (Finset.sum_le_sum h).trans
  norm_num [blockBound, Finset.sum_range_succ]
#print axioms endpoint_upper
#print axioms base_upper
#print axioms sum_upper
end DensityBlockResultRow192
