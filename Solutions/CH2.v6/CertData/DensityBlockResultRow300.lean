/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import CertData.DensityPointRow300
import Mathlib.Tactic.IntervalCases
import CertData.DensityBlockRow300_00
import CertData.DensityBlockRow300_01
import CertData.DensityBlockRow300_02
import CertData.DensityBlockRow300_03
import CertData.DensityBlockRow300_04
import CertData.DensityBlockRow300_05
import CertData.DensityBlockRow300_06
import CertData.DensityBlockRow300_07
import CertData.DensityBlockRow300_08
import CertData.DensityBlockRow300_09
import CertData.DensityBlockRow300_10
import CertData.DensityBlockRow300_11
import CertData.DensityBlockRow300_12
import CertData.DensityBlockRow300_13
import CertData.DensityBlockRow300_14
import CertData.DensityBlockRow300_15
import CertData.DensityBlockRow300_16
import CertData.DensityBlockRow300_17
import CertData.DensityBlockRow300_18
import CertData.DensityBlockRow300_19
import CertData.DensityBlockRow300_20
import CertData.DensityBlockRow300_21
import CertData.DensityBlockRow300_22
import CertData.DensityBlockRow300_23
import CertData.DensityBlockRow300_24
import CertData.DensityBlockRow300_25
import CertData.DensityBlockRow300_26
import CertData.DensityBlockRow300_27
import CertData.DensityBlockRow300_28
import CertData.DensityBlockRow300_29
import CertData.DensityBlockRow300_30
import CertData.DensityBlockRow300_31
set_option maxRecDepth 10000
open DensityNumeric
namespace DensityBlockResultRow300
theorem endpoint_upper : Q (7/8) 82 ≤ (18473 : ℝ) / 2000000 := DensityPointRow300.endpoint_upper
theorem base_upper : Real.exp (-(300:ℝ)/8) *
    (((82:ℝ)+(1:ℝ)/10^9)^2/(2*Real.pi)+(2+1/Real.pi)*((82:ℝ)+(1:ℝ)/10^9)) ≤ (1 : ℝ) / 10000000 := DensityPointRow300.base_upper

private noncomputable def blockBound (b : ℕ) : ℝ :=
  [(108251 : ℝ) / 50000000, (11847 : ℝ) / 12500000, (10377 : ℝ) / 25000000, (4547 : ℝ) / 25000000, (319 : ℝ) / 4000000, (7 : ℝ) / 200000, (1539 : ℝ) / 100000000, (339 : ℝ) / 50000000, (301 : ℝ) / 100000000, (27 : ℝ) / 20000000, (63 : ℝ) / 100000000, (31 : ℝ) / 100000000, (17 : ℝ) / 100000000, (1 : ℝ) / 10000000, (1 : ℝ) / 12500000, (3 : ℝ) / 50000000, (3 : ℝ) / 50000000, (3 : ℝ) / 50000000, (3 : ℝ) / 50000000, (3 : ℝ) / 50000000, (3 : ℝ) / 50000000, (3 : ℝ) / 50000000, (3 : ℝ) / 50000000, (3 : ℝ) / 50000000, (3 : ℝ) / 50000000, (3 : ℝ) / 50000000, (3 : ℝ) / 50000000, (3 : ℝ) / 50000000, (3 : ℝ) / 50000000, (3 : ℝ) / 50000000, (3 : ℝ) / 50000000, (3 : ℝ) / 50000000].getD b 0

theorem sum_upper : (∑ i ∈ Finset.range 512, cellTerm 300 82 i) ≤ (3863399999 : ℝ) / 1000000000000 := by
  rw [sum_512_blocks]
  have h : ∀ b ∈ Finset.range 32,
      (∑ k ∈ Finset.Icc (0 : ℕ) 15, cellTerm 300 82 (b * 16 + k)) ≤ blockBound b := by
    intro b hb
    have hb' : b < 32 := Finset.mem_range.mp hb
    interval_cases b
    · exact DensityBlockRow300.block_00
    · exact DensityBlockRow300.block_01
    · exact DensityBlockRow300.block_02
    · exact DensityBlockRow300.block_03
    · exact DensityBlockRow300.block_04
    · exact DensityBlockRow300.block_05
    · exact DensityBlockRow300.block_06
    · exact DensityBlockRow300.block_07
    · exact DensityBlockRow300.block_08
    · exact DensityBlockRow300.block_09
    · exact DensityBlockRow300.block_10
    · exact DensityBlockRow300.block_11
    · exact DensityBlockRow300.block_12
    · exact DensityBlockRow300.block_13
    · exact DensityBlockRow300.block_14
    · exact DensityBlockRow300.block_15
    · exact DensityBlockRow300.block_16
    · exact DensityBlockRow300.block_17
    · exact DensityBlockRow300.block_18
    · exact DensityBlockRow300.block_19
    · exact DensityBlockRow300.block_20
    · exact DensityBlockRow300.block_21
    · exact DensityBlockRow300.block_22
    · exact DensityBlockRow300.block_23
    · exact DensityBlockRow300.block_24
    · exact DensityBlockRow300.block_25
    · exact DensityBlockRow300.block_26
    · exact DensityBlockRow300.block_27
    · exact DensityBlockRow300.block_28
    · exact DensityBlockRow300.block_29
    · exact DensityBlockRow300.block_30
    · exact DensityBlockRow300.block_31
  apply (Finset.sum_le_sum h).trans
  norm_num [blockBound, Finset.sum_range_succ]
#print axioms endpoint_upper
#print axioms base_upper
#print axioms sum_upper
end DensityBlockResultRow300
