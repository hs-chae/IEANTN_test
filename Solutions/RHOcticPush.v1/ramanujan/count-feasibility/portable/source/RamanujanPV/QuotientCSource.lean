/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import RamanujanPV.QuotientCSourceV2
namespace RamanujanPV.QuotientCSource
abbrev sqrtFunction := QuotientCSourceV2.sqrtFunction
abbrev countFunction := QuotientCSourceV2.countFunction
abbrev functions := QuotientCSourceV2.functions
abbrev render := QuotientCSourceV2.render
abbrev actualSource := QuotientCSourceV2.actualSource
/-- The first direct binding attempt is archived with its failed render
proof. This canonical interface uses the completed exact-byte refinement. -/
theorem actual_source_bytes : render ()=some actualSource := QuotientCSourceV2.actual_source_bytes
theorem actual_source_checked : LCMSourcePV.RestrictedC.SourceCorresponds render actualSource () :=
  QuotientCSourceV2.actual_source_checked
#print axioms actual_source_bytes
#print axioms actual_source_checked
end RamanujanPV.QuotientCSource
