/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import CertData.DensityPointRow1000
import Mathlib.Tactic.IntervalCases
import CertData.DensityBlockRow1000_00
import CertData.DensityBlockRow1000_01
import CertData.DensityBlockRow1000_02
import CertData.DensityBlockRow1000_03
import CertData.DensityBlockRow1000_04
import CertData.DensityBlockRow1000_05
import CertData.DensityBlockRow1000_06
import CertData.DensityBlockRow1000_07
import CertData.DensityBlockRow1000_08
import CertData.DensityBlockRow1000_09
import CertData.DensityBlockRow1000_10
import CertData.DensityBlockRow1000_11
import CertData.DensityBlockRow1000_12
import CertData.DensityBlockRow1000_13
import CertData.DensityBlockRow1000_14
import CertData.DensityBlockRow1000_15
import CertData.DensityBlockRow1000_16
import CertData.DensityBlockRow1000_17
import CertData.DensityBlockRow1000_18
import CertData.DensityBlockRow1000_19
import CertData.DensityBlockRow1000_20
import CertData.DensityBlockRow1000_21
import CertData.DensityBlockRow1000_22
import CertData.DensityBlockRow1000_23
import CertData.DensityBlockRow1000_24
import CertData.DensityBlockRow1000_25
import CertData.DensityBlockRow1000_26
import CertData.DensityBlockRow1000_27
import CertData.DensityBlockRow1000_28
import CertData.DensityBlockRow1000_29
import CertData.DensityBlockRow1000_30
import CertData.DensityBlockRow1000_31
set_option maxRecDepth 10000
open DensityNumeric
namespace DensityBlockResultRow1000
theorem endpoint_upper : Q (7/8) 260 ≤ (18473 : ℝ) / 2000000 := DensityPointRow1000.endpoint_upper
theorem base_upper : Real.exp (-(1000:ℝ)/8) *
    (((260:ℝ)+(1:ℝ)/10^9)^2/(2*Real.pi)+(2+1/Real.pi)*((260:ℝ)+(1:ℝ)/10^9)) ≤ (1 : ℝ) / 10000000 := DensityPointRow1000.base_upper

private noncomputable def blockBound (b : ℕ) : ℝ :=
  [(21709 : ℝ) / 25000000, (2473 : ℝ) / 100000000, (19 : ℝ) / 25000000, (7 : ℝ) / 100000000, (3 : ℝ) / 50000000, (3 : ℝ) / 50000000, (3 : ℝ) / 50000000, (3 : ℝ) / 50000000, (3 : ℝ) / 50000000, (3 : ℝ) / 50000000, (3 : ℝ) / 50000000, (3 : ℝ) / 50000000, (3 : ℝ) / 50000000, (3 : ℝ) / 50000000, (3 : ℝ) / 50000000, (3 : ℝ) / 50000000, (3 : ℝ) / 50000000, (3 : ℝ) / 50000000, (3 : ℝ) / 50000000, (3 : ℝ) / 50000000, (3 : ℝ) / 50000000, (3 : ℝ) / 50000000, (3 : ℝ) / 50000000, (3 : ℝ) / 50000000, (3 : ℝ) / 50000000, (3 : ℝ) / 50000000, (3 : ℝ) / 50000000, (3 : ℝ) / 50000000, (3 : ℝ) / 50000000, (3 : ℝ) / 50000000, (3 : ℝ) / 50000000, (3 : ℝ) / 50000000].getD b 0

theorem sum_upper : (∑ i ∈ Finset.range 512, cellTerm 1000 260 i) ≤ (903399999 : ℝ) / 1000000000000 := by
  rw [sum_512_blocks]
  have h : ∀ b ∈ Finset.range 32,
      (∑ k ∈ Finset.Icc (0 : ℕ) 15, cellTerm 1000 260 (b * 16 + k)) ≤ blockBound b := by
    intro b hb
    have hb' : b < 32 := Finset.mem_range.mp hb
    interval_cases b
    · exact DensityBlockRow1000.block_00
    · exact DensityBlockRow1000.block_01
    · exact DensityBlockRow1000.block_02
    · exact DensityBlockRow1000.block_03
    · exact DensityBlockRow1000.block_04
    · exact DensityBlockRow1000.block_05
    · exact DensityBlockRow1000.block_06
    · exact DensityBlockRow1000.block_07
    · exact DensityBlockRow1000.block_08
    · exact DensityBlockRow1000.block_09
    · exact DensityBlockRow1000.block_10
    · exact DensityBlockRow1000.block_11
    · exact DensityBlockRow1000.block_12
    · exact DensityBlockRow1000.block_13
    · exact DensityBlockRow1000.block_14
    · exact DensityBlockRow1000.block_15
    · exact DensityBlockRow1000.block_16
    · exact DensityBlockRow1000.block_17
    · exact DensityBlockRow1000.block_18
    · exact DensityBlockRow1000.block_19
    · exact DensityBlockRow1000.block_20
    · exact DensityBlockRow1000.block_21
    · exact DensityBlockRow1000.block_22
    · exact DensityBlockRow1000.block_23
    · exact DensityBlockRow1000.block_24
    · exact DensityBlockRow1000.block_25
    · exact DensityBlockRow1000.block_26
    · exact DensityBlockRow1000.block_27
    · exact DensityBlockRow1000.block_28
    · exact DensityBlockRow1000.block_29
    · exact DensityBlockRow1000.block_30
    · exact DensityBlockRow1000.block_31
  apply (Finset.sum_le_sum h).trans
  norm_num [blockBound, Finset.sum_range_succ]
#print axioms endpoint_upper
#print axioms base_upper
#print axioms sum_upper
end DensityBlockResultRow1000
