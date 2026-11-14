/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedC.NumericRepresentation
import ScopedC.NatResultInvariants

namespace ScopedC.RationalInputs
open ScopedC.Machine ScopedC.NatWrapperCalls
open ScopedNumerical
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Actual runtime slots together with their mathematical contents. No desired
result, execution trace or pool acceptance is stored in this input description. -/
structure Data where
  magSlot : Nat
  denSlot : Nat
  magnitude : Nat
  denominator : Nat
  negative : Bool

namespace Data

def source (q : Data) : Value :=
  RecordCasts.rational q.magSlot (SignedNegCalls.bit q.negative) q.denSlot

def negativeWord (q : Data) : Nat :=
  if q.magnitude==0 then 0 else SignedNegCalls.bit (!q.negative)

def negatedSource (q : Data) : Value :=
  RationalNegCalls.value q.magSlot q.negativeWord q.denSlot

def mathematical (q : Data) : Rational := ⟨⟨q.magnitude,q.negative⟩,q.denominator⟩
def negativeMath (q : Data) : Rational := ⟨q.mathematical.num.negated,q.denominator⟩

def Live (s : State) (q : Data) : Prop :=
  NatArena.Borrow s.nats q.magSlot q.magnitude ∧ NatArena.Borrow s.nats q.denSlot q.denominator

theorem live_nats {s t : State} {q : Data} (same : t.nats=s.nats) (h : q.Live s) : q.Live t := by
  simpa only [Live,same] using h

theorem live_after {l : PoolCalls.PoolLayout} {s : State} {cells : List (Option Value)}
    {top high result : Nat} {q : Data} (h : q.Live s) :
    q.Live (binaryResult l s cells top high result) :=
  ⟨binary_result_preserves h.1,binary_result_preserves h.2⟩

theorem negativeWord_bound (q : Data) : q.negativeWord<2^32 := by
  unfold negativeWord
  split
  · decide
  · exact SignedNegCalls.bit_bound _

theorem cast {s : State} (fuel : Nat) (type : String) (normal : normalizeType type="Q")
    {q : Data} (h : q.Live s) : castValue Header.layout s (fuel+3) type q.source=some q.source :=
  RecordCasts.rational_record s fuel type normal h.1 h.2 (SignedNegCalls.bit_bound _)

theorem cast_negative {s : State} (fuel : Nat) (type : String) (normal : normalizeType type="Q")
    {q : Data} (h : q.Live s) :
    castValue Header.layout s (fuel+3) type q.negatedSource=some q.negatedSource :=
  RecordCasts.rational_record s fuel type normal h.1 h.2 q.negativeWord_bound

theorem initialized (q : Data) : Machine.initialized 1000 q.source=true := rfl
theorem negative_initialized (q : Data) : Machine.initialized 1000 q.negatedSource=true := rfl

theorem decoded {s : State} {q : Data} (h : q.Live s) (positive : 0<q.denominator) :
    NumericRepresentation.rational s q.source=some q.mathematical :=
  NumericRepresentation.rational_value _ h.1 h.2 positive

theorem negative_decoded {s : State} {q : Data} (h : q.Live s) (positive : 0<q.denominator) :
    NumericRepresentation.rational s q.negatedSource=some q.negativeMath :=
  NumericRepresentation.rational_negated _ h.1 h.2 positive

end Data
end ScopedC.RationalInputs
