/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedC.RationalAbsBody
import ScopedC.RationalPointBody
import ScopedNumerical.Arithmetic
import LeanCert.Core.IntervalRat.Basic

namespace ScopedC.NumericRepresentation
open ScopedC.Machine ScopedC.NatWrapperCalls
open ScopedNumerical
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Decode an actual source S record using live Nat-runtime storage. Reject
wrong types and every unsigned flag other than the represented bits 0 and 1. -/
def signed (s : State) : Value → Option Signed
  | .record tag [.natObject slot,.integer flag] => do
    if tag != "S" || flag.type != ⟨false,32⟩ then none else
    let magnitude ← NatArena.read s.nats slot
    if flag.number=0 then pure ⟨magnitude,false⟩
    else if flag.number=1 then pure ⟨magnitude,true⟩ else none
  | _ => none

/-- The denominator must be a live, strictly positive Nat. -/
def rational (s : State) : Value → Option Rational
  | .record tag [num,.natObject slot] => do
    if tag != "Q" then none else
    let numerator ← signed s num
    let denominator ← NatArena.read s.nats slot
    if 0<denominator then pure ⟨numerator,denominator⟩ else none
  | _ => none

/-- Decoding an RI also checks its required endpoint order. -/
def interval (s : State) : Value → Option LeanCert.Core.IntervalRat
  | .record tag [lo,hi] => do
    if tag != "RI" then none else
    let l ← rational s lo
    let h ← rational s hi
    if ordered : l.value≤h.value then pure ⟨l.value,h.value,ordered⟩ else none
  | _ => none

theorem signed_value {s : State} {slot n : Nat} (b : Bool)
    (live : NatArena.Borrow s.nats slot n) :
    signed s (SignedValues.value slot (SignedNegCalls.bit b))=some ⟨n,b⟩ := by
  cases b <;> simp [signed,SignedValues.value,unsigned32,SignedNegCalls.bit,
    NatArena.read_of_borrow live]

theorem rational_value {s : State} {mag n den d : Nat} (b : Bool)
    (magLive : NatArena.Borrow s.nats mag n) (denLive : NatArena.Borrow s.nats den d)
    (positive : 0<d) :
    rational s (RecordCasts.rational mag (SignedNegCalls.bit b) den)=some ⟨⟨n,b⟩,d⟩ := by
  have hs := signed_value b magLive
  simp only [rational,RecordCasts.rational,beq_self_eq_true,Bool.not_true,Bool.false_eq_true,↓reduceIte]
  rw [hs]
  simp [NatArena.read_of_borrow denLive,positive]

theorem rational_positive {s : State} {v : Value} {q : Rational}
    (h : rational s v=some q) : 0<q.den := by
  cases v <;> simp only [rational] at h <;> try contradiction
  rename_i tag xs
  split at h <;> try contradiction
  rename_i num slot he
  split at h <;> try contradiction
  cases hs : signed s num <;> simp only [hs,bind,Option.bind_none,Option.bind_some] at h <;> try contradiction
  rename_i numerator
  cases hd : NatArena.read s.nats slot <;> simp only [hd,bind,Option.bind_none,Option.bind_some] at h <;> try contradiction
  rename_i denominator
  split at h
  · cases h
    assumption
  · contradiction

theorem signed_negated {s : State} {slot n : Nat} (b : Bool)
    (live : NatArena.Borrow s.nats slot n) :
    signed s (SignedNegCalls.value slot (if n==0 then 0 else SignedNegCalls.bit (!b)))=
      some (Signed.negated ⟨n,b⟩) := by
  by_cases zero : n=0
  · simpa [SignedNegCalls.value,SignedValues.value,Signed.negated,Signed.make,SignedNegCalls.bit,zero]
      using signed_value false live
  · simpa [SignedNegCalls.value,SignedValues.value,Signed.negated,Signed.make,zero]
      using signed_value (!b) live

theorem rational_negated {s : State} {mag n den d : Nat} (b : Bool)
    (magLive : NatArena.Borrow s.nats mag n) (denLive : NatArena.Borrow s.nats den d)
    (positive : 0<d) :
    rational s (RationalNegCalls.value mag (if n==0 then 0 else SignedNegCalls.bit (!b)) den)=
      some ⟨Signed.negated ⟨n,b⟩,d⟩ := by
  have hs := signed_negated b magLive
  simp only [rational,RationalNegCalls.value,beq_self_eq_true,Bool.not_true,
    Bool.false_eq_true,↓reduceIte]
  rw [hs]
  simp [NatArena.read_of_borrow denLive,positive]

theorem interval_point {s : State} {mag n den d : Nat} (b : Bool)
    (magLive : NatArena.Borrow s.nats mag n) (denLive : NatArena.Borrow s.nats den d)
    (positive : 0<d) :
    interval s (IntervalCasts.value (RecordCasts.rational mag (SignedNegCalls.bit b) den)
      (RecordCasts.rational mag (SignedNegCalls.bit b) den))=
      some (LeanCert.Core.IntervalRat.singleton (Rational.value ⟨⟨n,b⟩,d⟩)) := by
  have hq := rational_value b magLive denLive positive
  simp [interval,IntervalCasts.value,hq,LeanCert.Core.IntervalRat.singleton]

end ScopedC.NumericRepresentation
