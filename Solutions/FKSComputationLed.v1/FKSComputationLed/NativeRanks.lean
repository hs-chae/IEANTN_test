/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/

import FKSComputationLed.Input
import FKSComputationLed.Support.BaseRuntime
import Mathlib
namespace FKSComputationLed.NativeRanks
open Input Sieve

def upper : Nat := 1000000000
def rankCheck (ps : Array UInt32) (x c : Nat) : Bool :=
  decide (2≤c ∧ c-2<ps.size ∧ ps[c-2]!.toNat≤x ∧
    (c-1=ps.size ∨ (c-1<ps.size ∧ x<ps[c-1]!.toNat)))
def ranksGate : Bool :=
  let ps := oddPrimeList upper
  cells.toList.all fun z => rankCheck ps z.a z.ca && rankCheck ps z.b z.cb
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
/-- New computation over the canonical existing proved sieve, not a hash or assumed prime list.
The prime coverage itself is V: old admitted source/native evidence already contained primes to2e9.
The closed gate provides all exact endpoint ranks used by the NEW Li envelope computation. -/
theorem all_ranks_checked : ranksGate = true := by native_decide
#print axioms all_ranks_checked
end FKSComputationLed.NativeRanks
