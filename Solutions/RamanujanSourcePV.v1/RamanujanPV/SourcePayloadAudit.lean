/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import RamanujanPV.CSource
import RamanujanPV.QuotientCSourceV2
import RamanujanPV.QuotientDriverSource
import RamanujanPV.SegmentCheckerSource
import RamanujanPV.FiniteExpSource

/-! A fresh comparison of the actual current files with the source strings
stored in every imported source-binding proof object. This supplements the
generic build helper's Lean-source hash with the exact include_str payloads. -/
namespace RamanujanPV.SourcePayloadAudit
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem trial_current : Source.actualSource = include_str "../c/verified_primecount.c" := by
  decide +kernel

theorem quotient_current : QuotientCSourceV2.actualSource =
    include_str "../c/verified_quotient_count.c" := by decide +kernel

theorem driver_current : QuotientDriverSource.actualSource =
    include_str "../c/verified_quotient_driver_n0.c" := by decide +kernel

theorem segment_current : SegmentCheckerSource.actualSource =
    include_str "../c/verified_segment_checker.c" := by decide +kernel

theorem exponential_current : FiniteExpSource.actualSource =
    include_str "../c/verified_finite_exp.c" := by decide +kernel

#print axioms trial_current
#print axioms quotient_current
#print axioms driver_current
#print axioms segment_current
#print axioms exponential_current
end RamanujanPV.SourcePayloadAudit
