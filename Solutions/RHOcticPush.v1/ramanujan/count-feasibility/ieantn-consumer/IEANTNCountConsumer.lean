/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import CountSourceFinal
import WordBytesBounded
import IEANTN.Vocabulary.PrimeCounting

/-! The same source-indexed execution supplies the numerical bytes and is
checked by generic application correctness.
Bounded byte injectivity then connects that output to the IEANTN real function.
The numerical byte witness comes from the existing exhaustive kernel count;
no new native output, physical trace, or ISO-C adequacy is claimed. -/
namespace RHOcticPush.IEANTNCount
open RamanujanPV.QuotientCMachine
open RamanujanPV.QuotientDriverInit RamanujanPV.QuotientDriverExecution
set_option autoImplicit false

/-- Consume the actual source-indexed run and its output, rather than a
standalone prime-count equality or an unused source/grammar conjunction. -/
theorem fixed_count_from_same_source_run :
    Nat.primeCounting 1490000000000 = 55206486339 := by
  obtain ⟨final, run, _buffered, committed⟩ := ColdCount.complete_actual_source_run
  have correct := CounterSyntax.every_source_success canonicalLayout 32000000 ⟨[], []⟩ run
  have mathematicalBytes : final.world.committed = wordBytes (Nat.primeCounting 1490000000000) := by
    simpa only [List.nil_append] using correct.2
  have equalBytes : wordBytes (Nat.primeCounting 1490000000000) = wordBytes 55206486339 :=
    mathematicalBytes.symm.trans committed
  have simpleBound : Nat.primeCounting 1490000000000 ≤ 1490000000000 + 1 := by
    exact Nat.count_le Nat.Prime
  have countBound : Nat.primeCounting 1490000000000 < 256^8 :=
    lt_of_le_of_lt simpleBound (by norm_num)
  exact wordBytes_injective_below countBound (by norm_num) equalBytes

/-- The existing fixed count about the actual IEANTN real-variable function.
Its proof uses the same-run source/output result before changing vocabulary. -/
theorem primeCounting_fixed_point :
    IEANTN.primeCounting ((1490000000000 : Nat) : ℝ) = (55206486339 : ℝ) := by
  have castValue : ((55206486339 : Nat) : ℝ) = (55206486339 : ℝ) := by norm_num
  have realValue := (congrArg (fun n : Nat => (n : ℝ)) fixed_count_from_same_source_run).trans castValue
  simpa only [IEANTN.primeCounting, Nat.floor_natCast] using realValue

#print axioms fixed_count_from_same_source_run
#print axioms primeCounting_fixed_point
end RHOcticPush.IEANTNCount
