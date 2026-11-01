/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import CertData.DensityPointRow80
import Mathlib.Tactic.IntervalCases
import CertData.DensityBlockRow80_00
import CertData.DensityBlockRow80_01
import CertData.DensityBlockRow80_02
import CertData.DensityBlockRow80_03
import CertData.DensityBlockRow80_04
import CertData.DensityBlockRow80_05
import CertData.DensityBlockRow80_06
import CertData.DensityBlockRow80_07
import CertData.DensityBlockRow80_08
import CertData.DensityBlockRow80_09
import CertData.DensityBlockRow80_10
import CertData.DensityBlockRow80_11
import CertData.DensityBlockRow80_12
import CertData.DensityBlockRow80_13
import CertData.DensityBlockRow80_14
import CertData.DensityBlockRow80_15
import CertData.DensityBlockRow80_16
import CertData.DensityBlockRow80_17
import CertData.DensityBlockRow80_18
import CertData.DensityBlockRow80_19
import CertData.DensityBlockRow80_20
import CertData.DensityBlockRow80_21
import CertData.DensityBlockRow80_22
import CertData.DensityBlockRow80_23
import CertData.DensityBlockRow80_24
import CertData.DensityBlockRow80_25
import CertData.DensityBlockRow80_26
import CertData.DensityBlockRow80_27
import CertData.DensityBlockRow80_28
import CertData.DensityBlockRow80_29
import CertData.DensityBlockRow80_30
import CertData.DensityBlockRow80_31
set_option maxRecDepth 10000
open DensityNumeric
namespace DensityBlockResultRow80
theorem endpoint_upper : Q (7/8) 45 ≤ (92393 : ℝ) / 10000000 := DensityPointRow80.endpoint_upper
theorem base_upper : Real.exp (-(80:ℝ)/8) *
    (((45:ℝ)+(1:ℝ)/10^9)^2/(2*Real.pi)+(2+1/Real.pi)*((45:ℝ)+(1:ℝ)/10^9)) ≤ (96841 : ℝ) / 5000000 := DensityPointRow80.base_upper

private noncomputable def blockBound (b : ℕ) : ℝ :=
  [(80891 : ℝ) / 25000000, (334543 : ℝ) / 100000000, (8651 : ℝ) / 2500000, (358089 : ℝ) / 100000000, (370727 : ℝ) / 100000000, (95999 : ℝ) / 25000000, (397939 : ℝ) / 100000000, (82521 : ℝ) / 20000000, (26753 : ℝ) / 6250000, (444327 : ℝ) / 100000000, (230753 : ℝ) / 50000000, (239829 : ℝ) / 50000000, (249431 : ℝ) / 50000000, (519207 : ℝ) / 100000000, (540791 : ℝ) / 100000000, (281863 : ℝ) / 50000000, (588133 : ℝ) / 100000000, (307077 : ℝ) / 50000000, (80243 : ℝ) / 12500000, (671681 : ℝ) / 100000000, (351783 : ℝ) / 50000000, (737829 : ℝ) / 100000000, (193683 : ℝ) / 25000000, (32583 : ℝ) / 4000000, (857703 : ℝ) / 100000000, (180903 : ℝ) / 20000000, (38219 : ℝ) / 4000000, (1011119 : ℝ) / 100000000, (268019 : ℝ) / 25000000, (284771 : ℝ) / 25000000, (121301 : ℝ) / 10000000, (1294881 : ℝ) / 100000000].getD b 0

theorem sum_upper : (∑ i ∈ Finset.range 512, cellTerm 80 45 i) ≤ (208582499999 : ℝ) / 1000000000000 := by
  rw [sum_512_blocks]
  have h : ∀ b ∈ Finset.range 32,
      (∑ k ∈ Finset.Icc (0 : ℕ) 15, cellTerm 80 45 (b * 16 + k)) ≤ blockBound b := by
    intro b hb
    have hb' : b < 32 := Finset.mem_range.mp hb
    interval_cases b
    · exact DensityBlockRow80.block_00
    · exact DensityBlockRow80.block_01
    · exact DensityBlockRow80.block_02
    · exact DensityBlockRow80.block_03
    · exact DensityBlockRow80.block_04
    · exact DensityBlockRow80.block_05
    · exact DensityBlockRow80.block_06
    · exact DensityBlockRow80.block_07
    · exact DensityBlockRow80.block_08
    · exact DensityBlockRow80.block_09
    · exact DensityBlockRow80.block_10
    · exact DensityBlockRow80.block_11
    · exact DensityBlockRow80.block_12
    · exact DensityBlockRow80.block_13
    · exact DensityBlockRow80.block_14
    · exact DensityBlockRow80.block_15
    · exact DensityBlockRow80.block_16
    · exact DensityBlockRow80.block_17
    · exact DensityBlockRow80.block_18
    · exact DensityBlockRow80.block_19
    · exact DensityBlockRow80.block_20
    · exact DensityBlockRow80.block_21
    · exact DensityBlockRow80.block_22
    · exact DensityBlockRow80.block_23
    · exact DensityBlockRow80.block_24
    · exact DensityBlockRow80.block_25
    · exact DensityBlockRow80.block_26
    · exact DensityBlockRow80.block_27
    · exact DensityBlockRow80.block_28
    · exact DensityBlockRow80.block_29
    · exact DensityBlockRow80.block_30
    · exact DensityBlockRow80.block_31
  apply (Finset.sum_le_sum h).trans
  norm_num [blockBound, Finset.sum_range_succ]
#print axioms endpoint_upper
#print axioms base_upper
#print axioms sum_upper
end DensityBlockResultRow80
