/- Copyright (c) 2026 IEANTN contributors. Apache-2.0. -/
import ScopedIO.SourceWith
import Mathlib.Data.List.TakeDrop

namespace ScopedIO
open ScopedC ScopedC.Machine
set_option autoImplicit false
set_option maxHeartbeats 0

/-- Ghost state of a generic C output stream. `accepted` records bytes
accepted by stdio; `delivered` counts the count known delivered to the host.
It does not model FILE implementation fields or durable disk storage. The
remaining unwritten bytes are an abstraction of knowledge, not a claim about
the concrete libc buffering strategy. -/
structure Stream where
  accepted : List Nat
  delivered : Nat
  error : Bool
  deriving DecidableEq

def Stream.Valid (st : Stream) : Prop :=
  (∀ b ∈ st.accepted, b < 256) ∧ st.delivered ≤ st.accepted.length

/-- Failure may accept any count before reporting a negative return value.
No operation is assumed successful. This is a disclosed generic stdio
contract, not an application output or SuccessfulEffects premise. -/
def writeBytes (before : Stream) (bytes : List Nat) (succeed : Bool) (count : Nat) : Stream :=
  if succeed then {before with accepted:=before.accepted++bytes}
  else {before with accepted:=before.accepted++bytes.take count,error:=true}

def flush (before : Stream) (succeed : Bool) (count : Nat) : Stream :=
  if succeed then {before with delivered:=before.accepted.length}
  else {before with delivered:=max before.delivered (min count before.accepted.length),error:=true}

theorem write_valid {before : Stream} (h : before.Valid) {bytes : List Nat}
    (hb : ∀ b ∈ bytes, b < 256) (succeed : Bool) (count : Nat) :
    (writeBytes before bytes succeed count).Valid := by
  rcases h with ⟨hbytes,hdelivered⟩
  cases succeed <;> constructor
  · intro b mem
    have hm : b ∈ before.accepted ∨ b ∈ bytes.take count := by simpa [writeBytes] using mem
    exact hm.elim (hbytes b) (fun h => hb b (List.mem_of_mem_take h))
  · simpa [writeBytes] using hdelivered.trans (Nat.le_add_right before.accepted.length (bytes.take count).length)
  · intro b mem
    have hm : b ∈ before.accepted ∨ b ∈ bytes := by simpa [writeBytes] using mem
    exact hm.elim (hbytes b) (hb b)
  · simpa [writeBytes] using hdelivered.trans (Nat.le_add_right before.accepted.length bytes.length)

theorem flush_valid {before : Stream} (h : before.Valid) (succeed : Bool) (count : Nat) :
    (flush before succeed count).Valid := by
  cases succeed <;> constructor
  · exact h.1
  · exact max_le h.2 (min_le_right _ _)
  · exact h.1
  · exact le_rfl

theorem successful_write (before : Stream) (bytes : List Nat) (count : Nat) :
    (writeBytes before bytes true count).accepted = before.accepted++bytes := rfl

theorem failed_write_records_error (before : Stream) (bytes : List Nat) (count : Nat) :
    (writeBytes before bytes false count).error = true := rfl

theorem successful_flush_delivers_all (before : Stream) (count : Nat) :
    (flush before true count).delivered = before.accepted.length ∧
      (flush before true count).accepted = before.accepted := ⟨rfl,rfl⟩

end ScopedIO
