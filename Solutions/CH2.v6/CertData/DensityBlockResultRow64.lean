/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import CertData.DensityPointRow64
import Mathlib.Tactic.IntervalCases
import CertData.DensityBlockRow64_00
import CertData.DensityBlockRow64_01
import CertData.DensityBlockRow64_02
import CertData.DensityBlockRow64_03
import CertData.DensityBlockRow64_04
import CertData.DensityBlockRow64_05
import CertData.DensityBlockRow64_06
import CertData.DensityBlockRow64_07
import CertData.DensityBlockRow64_08
import CertData.DensityBlockRow64_09
import CertData.DensityBlockRow64_10
import CertData.DensityBlockRow64_11
import CertData.DensityBlockRow64_12
import CertData.DensityBlockRow64_13
import CertData.DensityBlockRow64_14
import CertData.DensityBlockRow64_15
import CertData.DensityBlockRow64_16
import CertData.DensityBlockRow64_17
import CertData.DensityBlockRow64_18
import CertData.DensityBlockRow64_19
import CertData.DensityBlockRow64_20
import CertData.DensityBlockRow64_21
import CertData.DensityBlockRow64_22
import CertData.DensityBlockRow64_23
import CertData.DensityBlockRow64_24
import CertData.DensityBlockRow64_25
import CertData.DensityBlockRow64_26
import CertData.DensityBlockRow64_27
import CertData.DensityBlockRow64_28
import CertData.DensityBlockRow64_29
import CertData.DensityBlockRow64_30
import CertData.DensityBlockRow64_31
set_option maxRecDepth 10000
open DensityNumeric
namespace DensityBlockResultRow64
theorem endpoint_upper : Q (7/8) 44 ≤ (18483 : ℝ) / 2000000 := DensityPointRow64.endpoint_upper
theorem base_upper : Real.exp (-(64:ℝ)/8) *
    (((44:ℝ)+(1:ℝ)/10^9)^2/(2*Real.pi)+(2+1/Real.pi)*((44:ℝ)+(1:ℝ)/10^9)) ≤ (171979 : ℝ) / 1250000 := DensityPointRow64.base_upper

private noncomputable def blockBound (b : ℕ) : ℝ :=
  [(167031 : ℝ) / 50000000, (367691 : ℝ) / 100000000, (404879 : ℝ) / 100000000, (223013 : ℝ) / 50000000, (7681 : ℝ) / 1562500, (27103 : ℝ) / 5000000, (23921 : ℝ) / 4000000, (660123 : ℝ) / 100000000, (18227 : ℝ) / 2500000, (805717 : ℝ) / 100000000, (890967 : ℝ) / 100000000, (985887 : ℝ) / 100000000, (545839 : ℝ) / 50000000, (1209711 : ℝ) / 100000000, (1341549 : ℝ) / 100000000, (297797 : ℝ) / 20000000, (1654073 : ℝ) / 100000000, (1839177 : ℝ) / 100000000, (81881 : ℝ) / 4000000, (228077 : ℝ) / 10000000, (318009 : ℝ) / 12500000, (2841191 : ℝ) / 100000000, (1588549 : ℝ) / 50000000, (177881 : ℝ) / 5000000, (1994803 : ℝ) / 50000000, (224057 : ℝ) / 5000000, (25209 : ℝ) / 500000, (2841489 : ℝ) / 50000000, (1283657 : ℝ) / 20000000, (1452811 : ℝ) / 20000000, (1029997 : ℝ) / 12500000, (9369897 : ℝ) / 100000000].getD b 0

theorem sum_upper : (∑ i ∈ Finset.range 512, cellTerm 64 44 i) ≤ (828175299999 : ℝ) / 1000000000000 := by
  rw [sum_512_blocks]
  have h : ∀ b ∈ Finset.range 32,
      (∑ k ∈ Finset.Icc (0 : ℕ) 15, cellTerm 64 44 (b * 16 + k)) ≤ blockBound b := by
    intro b hb
    have hb' : b < 32 := Finset.mem_range.mp hb
    interval_cases b
    · exact DensityBlockRow64.block_00
    · exact DensityBlockRow64.block_01
    · exact DensityBlockRow64.block_02
    · exact DensityBlockRow64.block_03
    · exact DensityBlockRow64.block_04
    · exact DensityBlockRow64.block_05
    · exact DensityBlockRow64.block_06
    · exact DensityBlockRow64.block_07
    · exact DensityBlockRow64.block_08
    · exact DensityBlockRow64.block_09
    · exact DensityBlockRow64.block_10
    · exact DensityBlockRow64.block_11
    · exact DensityBlockRow64.block_12
    · exact DensityBlockRow64.block_13
    · exact DensityBlockRow64.block_14
    · exact DensityBlockRow64.block_15
    · exact DensityBlockRow64.block_16
    · exact DensityBlockRow64.block_17
    · exact DensityBlockRow64.block_18
    · exact DensityBlockRow64.block_19
    · exact DensityBlockRow64.block_20
    · exact DensityBlockRow64.block_21
    · exact DensityBlockRow64.block_22
    · exact DensityBlockRow64.block_23
    · exact DensityBlockRow64.block_24
    · exact DensityBlockRow64.block_25
    · exact DensityBlockRow64.block_26
    · exact DensityBlockRow64.block_27
    · exact DensityBlockRow64.block_28
    · exact DensityBlockRow64.block_29
    · exact DensityBlockRow64.block_30
    · exact DensityBlockRow64.block_31
  apply (Finset.sum_le_sum h).trans
  norm_num [blockBound, Finset.sum_range_succ]
#print axioms endpoint_upper
#print axioms base_upper
#print axioms sum_upper
end DensityBlockResultRow64
