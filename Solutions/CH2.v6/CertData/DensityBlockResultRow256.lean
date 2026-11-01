/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import CertData.DensityPointRow256
import Mathlib.Tactic.IntervalCases
import CertData.DensityBlockRow256_00
import CertData.DensityBlockRow256_01
import CertData.DensityBlockRow256_02
import CertData.DensityBlockRow256_03
import CertData.DensityBlockRow256_04
import CertData.DensityBlockRow256_05
import CertData.DensityBlockRow256_06
import CertData.DensityBlockRow256_07
import CertData.DensityBlockRow256_08
import CertData.DensityBlockRow256_09
import CertData.DensityBlockRow256_10
import CertData.DensityBlockRow256_11
import CertData.DensityBlockRow256_12
import CertData.DensityBlockRow256_13
import CertData.DensityBlockRow256_14
import CertData.DensityBlockRow256_15
import CertData.DensityBlockRow256_16
import CertData.DensityBlockRow256_17
import CertData.DensityBlockRow256_18
import CertData.DensityBlockRow256_19
import CertData.DensityBlockRow256_20
import CertData.DensityBlockRow256_21
import CertData.DensityBlockRow256_22
import CertData.DensityBlockRow256_23
import CertData.DensityBlockRow256_24
import CertData.DensityBlockRow256_25
import CertData.DensityBlockRow256_26
import CertData.DensityBlockRow256_27
import CertData.DensityBlockRow256_28
import CertData.DensityBlockRow256_29
import CertData.DensityBlockRow256_30
import CertData.DensityBlockRow256_31
set_option maxRecDepth 10000
open DensityNumeric
namespace DensityBlockResultRow256
theorem endpoint_upper : Q (7/8) 73 ≤ (18473 : ℝ) / 2000000 := DensityPointRow256.endpoint_upper
theorem base_upper : Real.exp (-(256:ℝ)/8) *
    (((73:ℝ)+(1:ℝ)/10^9)^2/(2*Real.pi)+(2+1/Real.pi)*((73:ℝ)+(1:ℝ)/10^9)) ≤ (1 : ℝ) / 10000000 := DensityPointRow256.base_upper

private noncomputable def blockBound (b : ℕ) : ℝ :=
  [(233459 : ℝ) / 100000000, (30341 : ℝ) / 25000000, (63119 : ℝ) / 100000000, (16421 : ℝ) / 50000000, (17097 : ℝ) / 100000000, (4453 : ℝ) / 50000000, (2321 : ℝ) / 50000000, (2423 : ℝ) / 100000000, (633 : ℝ) / 50000000, (663 : ℝ) / 100000000, (349 : ℝ) / 100000000, (37 : ℝ) / 20000000, (99 : ℝ) / 100000000, (11 : ℝ) / 20000000, (31 : ℝ) / 100000000, (19 : ℝ) / 100000000, (13 : ℝ) / 100000000, (9 : ℝ) / 100000000, (7 : ℝ) / 100000000, (7 : ℝ) / 100000000, (3 : ℝ) / 50000000, (3 : ℝ) / 50000000, (3 : ℝ) / 50000000, (3 : ℝ) / 50000000, (3 : ℝ) / 50000000, (3 : ℝ) / 50000000, (3 : ℝ) / 50000000, (3 : ℝ) / 50000000, (3 : ℝ) / 50000000, (3 : ℝ) / 50000000, (3 : ℝ) / 50000000, (3 : ℝ) / 50000000].getD b 0

theorem sum_upper : (∑ i ∈ Finset.range 512, cellTerm 256 73 i) ≤ (4873399999 : ℝ) / 1000000000000 := by
  rw [sum_512_blocks]
  have h : ∀ b ∈ Finset.range 32,
      (∑ k ∈ Finset.Icc (0 : ℕ) 15, cellTerm 256 73 (b * 16 + k)) ≤ blockBound b := by
    intro b hb
    have hb' : b < 32 := Finset.mem_range.mp hb
    interval_cases b
    · exact DensityBlockRow256.block_00
    · exact DensityBlockRow256.block_01
    · exact DensityBlockRow256.block_02
    · exact DensityBlockRow256.block_03
    · exact DensityBlockRow256.block_04
    · exact DensityBlockRow256.block_05
    · exact DensityBlockRow256.block_06
    · exact DensityBlockRow256.block_07
    · exact DensityBlockRow256.block_08
    · exact DensityBlockRow256.block_09
    · exact DensityBlockRow256.block_10
    · exact DensityBlockRow256.block_11
    · exact DensityBlockRow256.block_12
    · exact DensityBlockRow256.block_13
    · exact DensityBlockRow256.block_14
    · exact DensityBlockRow256.block_15
    · exact DensityBlockRow256.block_16
    · exact DensityBlockRow256.block_17
    · exact DensityBlockRow256.block_18
    · exact DensityBlockRow256.block_19
    · exact DensityBlockRow256.block_20
    · exact DensityBlockRow256.block_21
    · exact DensityBlockRow256.block_22
    · exact DensityBlockRow256.block_23
    · exact DensityBlockRow256.block_24
    · exact DensityBlockRow256.block_25
    · exact DensityBlockRow256.block_26
    · exact DensityBlockRow256.block_27
    · exact DensityBlockRow256.block_28
    · exact DensityBlockRow256.block_29
    · exact DensityBlockRow256.block_30
    · exact DensityBlockRow256.block_31
  apply (Finset.sum_le_sum h).trans
  norm_num [blockBound, Finset.sum_range_succ]
#print axioms endpoint_upper
#print axioms base_upper
#print axioms sum_upper
end DensityBlockResultRow256
