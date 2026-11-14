/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedC.DyadicCasts
import ScopedC.NumericRepresentation
import ScopedC.NatResultInvariants
import LeanCert.Core.IntervalDyadic

namespace ScopedC.DyadicRepresentation
open ScopedC.Machine ScopedC.NatWrapperCalls
open ScopedNumerical LeanCert.Core
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

structure Endpoint where
  slot : Nat
  magnitude : Nat
  negative : Bool

namespace Endpoint

def source (e : Endpoint) : Value := SignedValues.value e.slot (SignedNegCalls.bit e.negative)
def mathematical (e : Endpoint) : Signed := ⟨e.magnitude,e.negative⟩
def negativeWord (e : Endpoint) : Nat := if e.magnitude==0 then 0 else SignedNegCalls.bit (!e.negative)
def negativeSource (e : Endpoint) : Value := SignedNegCalls.value e.slot e.negativeWord

def Live (s : State) (e : Endpoint) : Prop := NatArena.Borrow s.nats e.slot e.magnitude

theorem live_after {l : PoolCalls.PoolLayout} {s : State} {cells : List (Option Value)}
    {top high result : Nat} {e : Endpoint} (h : e.Live s) :
    e.Live (binaryResult l s cells top high result) := binary_result_preserves h

theorem negativeWord_bound (e : Endpoint) : e.negativeWord<2^32 := by
  unfold negativeWord
  split
  · decide
  · exact SignedNegCalls.bit_bound _

theorem cast {s : State} (fuel : Nat) (type : String) (normal : normalizeType type="S")
    {e : Endpoint} (h : e.Live s) : castValue Header.layout s (fuel+2) type e.source=some e.source :=
  RecordCasts.signed s fuel type normal h (SignedNegCalls.bit_bound _)

theorem cast_negative {s : State} (fuel : Nat) (type : String) (normal : normalizeType type="S")
    {e : Endpoint} (h : e.Live s) :
    castValue Header.layout s (fuel+2) type e.negativeSource=some e.negativeSource :=
  RecordCasts.signed s fuel type normal h e.negativeWord_bound

theorem decoded {s : State} {e : Endpoint} (h : e.Live s) :
    NumericRepresentation.signed s e.source=some e.mathematical :=
  NumericRepresentation.signed_value _ h

theorem negative_decoded {s : State} {e : Endpoint} (h : e.Live s) :
    NumericRepresentation.signed s e.negativeSource=some e.mathematical.negated :=
  NumericRepresentation.signed_negated _ h

end Endpoint

/-- Source I always stores implicit exponent -100. This does not assert equality
with an arbitrary coarser old Dyadic representation of the same value. -/
def words100 (lo hi : Int) (ordered : lo≤hi) : IntervalDyadic :=
  ⟨⟨lo,-100⟩,⟨hi,-100⟩,by
    simp only [LeanCert.Core.Dyadic.toRat,show ¬(-100:Int)≥0 by decide,↓reduceIte]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact_mod_cast ordered⟩

def flag : Value → Option Bool
  | .integer v =>
    if v.type != ⟨false,32⟩ then none else
    if v.number=0 then some false else if v.number=1 then some true else none
  | _ => none

theorem flag_bit (b : Bool) : flag (unsigned32 (SignedNegCalls.bit b))=some b := by
  cases b <;> rfl

/-- The exact source I decoder validates both sign flags, the domain flag,
live magnitudes and interval order before producing the old mathematical type. -/
def interval (s : State) : Value → Option (IntervalDyadic × Bool)
  | .record tag [lo,hi,ok] => do
    if tag != "I" then none else
    let l ← NumericRepresentation.signed s lo
    let h ← NumericRepresentation.signed s hi
    let valid ← flag ok
    if ordered : l.value≤h.value then pure (words100 l.value h.value ordered,valid) else none
  | _ => none

theorem decoded_interval {s : State} (lo hi : Endpoint) (ok : Bool)
    (hl : lo.Live s) (hh : hi.Live s) (ordered : lo.mathematical.value≤hi.mathematical.value) :
    interval s (DyadicCasts.value lo.source hi.source ok)=
      some (words100 lo.mathematical.value hi.mathematical.value ordered,ok) := by
  have dl := Endpoint.decoded hl
  have dh := Endpoint.decoded hh
  simp [interval,DyadicCasts.value,dl,dh,flag_bit,ordered]

theorem decoded_negative_interval {s : State} (lo hi : Endpoint) (ok : Bool)
    (hl : lo.Live s) (hh : hi.Live s) (ordered : lo.mathematical.value≤hi.mathematical.value) :
    interval s (DyadicCasts.value hi.negativeSource lo.negativeSource ok)=
      some (IntervalDyadic.neg (words100 lo.mathematical.value hi.mathematical.value ordered),ok) := by
  have dl := Endpoint.negative_decoded hl
  have dh := Endpoint.negative_decoded hh
  simp [interval,DyadicCasts.value,dl,dh,flag_bit,Signed.value_negated,neg_le_neg_iff,ordered,
    words100,IntervalDyadic.neg,LeanCert.Core.Dyadic.neg]

end ScopedC.DyadicRepresentation
