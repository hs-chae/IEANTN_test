/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/

import FKSComputationLed.Support.SieveRuntime
namespace FKSComputationLed.Sieve
/-- Tail-recursive collection, inspecting precisely the odd candidates in order. -/
def collectOdd (flags : Array Bool) (next remaining : Nat) (acc : Array UInt32) : Array UInt32 :=
  match remaining with
  | 0 => acc
  | remaining+1 =>
    let out := if sieveRead flags next then acc.push (UInt32.ofNat next) else acc
    collectOdd flags (next+2) remaining out

/-- The complete odd-prime list through U is generated from the proved executable sieve. -/
def oddPrimeList (U : Nat) : Array UInt32 :=
  let flags := primeSieve U
  collectOdd flags 3 ((U-1)/2) #[]


end FKSComputationLed.Sieve
