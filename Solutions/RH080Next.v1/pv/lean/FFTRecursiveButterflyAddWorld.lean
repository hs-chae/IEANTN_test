/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTRecursiveButterflyAddInvariant
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
namespace RH080Next.FFTPV.RecursiveSource

/-- Actual output/work word functions with the proved source operand facts.
This contains no machine state or presumed execution result. -/
structure AddWorld (left : Nat) where
  output : Nat → Nat
  work : Nat → Nat
  facts : AddInvariant left output work

def addWorldInput {total : Nat} (buffers : Buffers total)
    (start index step n half j : Nat) (shape : IndexShape start index step n total)
    (split : n=2*half) (active : j<half) (input table : Nat → Nat) (i : Fin 4)
    (world : AddWorld (start+j)) : AddSource.Input :=
  butterflyAddInput buffers start index step n half j shape split active i input table
    world.output world.work world.facts.leftNormalized world.facts.tempDigits world.facts.tempSigns

def addWorldAdvance {total : Nat} (buffers : Buffers total)
    (start index step n half j : Nat) (shape : IndexShape start index step n total)
    (split : n=2*half) (active : j<half) (input table : Nat → Nat) (i : Fin 4)
    (world : AddWorld (start+j)) : AddWorld (start+j) :=
  {output := addOutputData i (addWorldInput buffers start index step n half j shape split active input table i world) world.output
   work := addWorkData i (addWorldInput buffers start index step n half j shape split active input table i world) world.work
   facts := add_invariant_after buffers start index step n half j shape split active i input table
     world.output world.work world.facts}

def addWorldFour {total : Nat} (buffers : Buffers total)
    (start index step n half j : Nat) (shape : IndexShape start index step n total)
    (split : n=2*half) (active : j<half) (input table : Nat → Nat) (world : AddWorld (start+j)) : AddWorld (start+j) :=
  let next := fun i => addWorldAdvance buffers start index step n half j shape split active input table i
  next 3 (next 2 (next 1 (next 0 world)))

end RH080Next.FFTPV.RecursiveSource
