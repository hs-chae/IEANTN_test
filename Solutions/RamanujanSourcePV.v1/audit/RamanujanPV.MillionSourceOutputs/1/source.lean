/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import RamanujanPV.QuotientCountRealization
import RamanujanPV.DemandMillionPair.Final

/-! Concrete numerical outputs of the actual optimized C source. The generated
paired numerical proof must be regenerated and kernel-compiled first. These
are source-function results; the fixed N0 main is a separate application. -/
namespace RamanujanPV.MillionSourceOutputs

theorem million : QuotientCCell.SourceExecution 1000000 78498 :=
  QuotientCountRealization.source_execution_from_kernel_value (by norm_num) (by norm_num)
    DemandMillionPair.pi_1000000

theorem scaled_million : QuotientCCell.SourceExecution 367879 31377 :=
  QuotientCountRealization.source_execution_from_kernel_value (by norm_num) (by norm_num)
    DemandMillionPair.pi_367879

#print axioms million
#print axioms scaled_million
end RamanujanPV.MillionSourceOutputs
