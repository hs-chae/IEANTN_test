/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/

import FKSComputationLed.Support.SieveMath

namespace FKSComputationLed.SieveMath
open FKSComputationLed.Sieve

theorem collectOdd_strictSorted_counter
    (flags : Array Bool) (remaining next : Nat) (acc : Array UInt32)
    (hacc : acc.toList.Pairwise (fun a b => a.toNat < b.toNat))
    (hbelow : ∀ w ∈ acc, w.toNat < next)
    (hbound : next + 2*remaining ≤ UInt32.size) :
    (collectOdd flags next remaining acc).toList.Pairwise (fun a b => a.toNat < b.toNat) := by
  induction remaining generalizing next acc with
  | zero => simpa [collectOdd] using hacc
  | succ remaining ih =>
    have hnext : next < UInt32.size := by omega
    have hexact : (UInt32.ofNat next).toNat = next := UInt32.toNat_ofNat_of_lt' hnext
    simp only [collectOdd]
    split_ifs with hflag
    · apply ih
      · rw [Array.toList_push, List.pairwise_append]
        refine ⟨hacc, by simp, ?_⟩
        intro a ha b hb
        simp only [List.mem_singleton] at hb
        subst b
        rw [hexact]
        exact hbelow a (by simpa using ha)
      · intro w hw
        rcases Array.mem_push.mp hw with hw | hw
        · have hh := hbelow w hw
          omega
        · subst w
          rw [hexact]
          omega
      · omega
    · apply ih (next+2) acc hacc
      · intro w hw
        have hh := hbelow w hw
        omega
      · omega

theorem oddPrimeList_strictSorted_counter (U : Nat) (hU : U ≤ 2000000000) :
    (oddPrimeList U).toList.Pairwise (fun a b => a.toNat < b.toNat) := by
  unfold oddPrimeList
  apply collectOdd_strictSorted_counter
  · simp
  · simp
  · change 3 + 2*((U-1)/2) ≤ 4294967296
    omega

#print axioms oddPrimeList_strictSorted_counter
end FKSComputationLed.SieveMath
