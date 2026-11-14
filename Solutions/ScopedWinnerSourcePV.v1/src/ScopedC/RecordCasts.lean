/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedC.SignedValues

namespace ScopedC.RecordCasts
open ScopedC.Machine ScopedC.NatWrapperCalls
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Two structural levels suffice for S: its actual fields are N and unsigned. -/
theorem signed_fields (s : State) (fuel slot n neg : Nat)
    (live : NatArena.Borrow s.nats slot n) (bound : neg<2^32) :
    ([ ("mag","N"),("neg","unsigned") ].zip [.natObject slot,unsigned32 neg]).mapM
      (fun item => castValue Header.layout s (fuel+1) item.1.2 item.2)=
      some [.natObject slot,unsigned32 neg] := by
  change (do
    let x ← castValue Header.layout s (fuel+1) "N" (.natObject slot)
    let y ← castValue Header.layout s (fuel+1) "unsigned" (unsigned32 neg)
    pure [x,y])=some [.natObject slot,unsigned32 neg]
  rw [PositiveCasts.cast_N Header.layout s fuel slot n live,
    PositiveCasts.cast_unsigned s fuel neg bound]
  rfl

theorem signed (s : State) (fuel : Nat) (type : String)
    (normalize : normalizeType type="S") {slot n neg : Nat}
    (live : NatArena.Borrow s.nats slot n) (bound : neg<2^32) :
    castValue Header.layout s (fuel+2) type (SignedValues.value slot neg)=
      some (SignedValues.value slot neg) := by
  exact TypedFrames.cast_record Header.layout s (fuel+1) type "S"
    [("mag","N"),("neg","unsigned")] [.natObject slot,unsigned32 neg] [.natObject slot,unsigned32 neg]
    normalize (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) rfl (signed_fields s fuel slot n neg live bound)

theorem signed_aggregate (s : State) (fuel : Nat) {slot n neg : Nat}
    (live : NatArena.Borrow s.nats slot n) (bound : neg<2^32) :
    castValue Header.layout s (fuel+2) "S" (.aggregate [.natObject slot,unsigned32 neg])=
      some (SignedValues.value slot neg) := by
  exact TypedFrames.cast_aggregate Header.layout s (fuel+1) "S" "S"
    [("mag","N"),("neg","unsigned")] [.natObject slot,unsigned32 neg] [.natObject slot,unsigned32 neg]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) rfl (signed_fields s fuel slot n neg live bound)

def rational (mag neg den : Nat) : Value :=
  .record "Q" [SignedValues.value mag neg,.natObject den]

/-- Three structural levels suffice for Q, including its nested S numerator. -/
theorem rational_fields (s : State) (fuel mag n neg den d : Nat)
    (magLive : NatArena.Borrow s.nats mag n) (denLive : NatArena.Borrow s.nats den d)
    (bound : neg<2^32) :
    ([("num","S"),("den","N")].zip [SignedValues.value mag neg,.natObject den]).mapM
      (fun item => castValue Header.layout s (fuel+2) item.1.2 item.2)=
      some [SignedValues.value mag neg,.natObject den] := by
  change (do
    let x ← castValue Header.layout s (fuel+2) "S" (SignedValues.value mag neg)
    let y ← castValue Header.layout s (fuel+2) "N" (.natObject den)
    pure [x,y])=some [SignedValues.value mag neg,.natObject den]
  rw [signed s fuel "S" (by decide +kernel) magLive bound,
    PositiveCasts.cast_N Header.layout s (fuel+1) den d denLive]
  rfl

theorem rational_record (s : State) (fuel : Nat) (type : String)
    (normalize : normalizeType type="Q") {mag n neg den d : Nat}
    (magLive : NatArena.Borrow s.nats mag n) (denLive : NatArena.Borrow s.nats den d)
    (bound : neg<2^32) :
    castValue Header.layout s (fuel+3) type (rational mag neg den)=
      some (rational mag neg den) := by
  exact TypedFrames.cast_record Header.layout s (fuel+2) type "Q"
    [("num","S"),("den","N")] [SignedValues.value mag neg,.natObject den]
    [SignedValues.value mag neg,.natObject den] normalize
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) rfl (rational_fields s fuel mag n neg den d magLive denLive bound)

theorem rational_aggregate (s : State) (fuel : Nat) {mag n neg den d : Nat}
    (magLive : NatArena.Borrow s.nats mag n) (denLive : NatArena.Borrow s.nats den d)
    (bound : neg<2^32) :
    castValue Header.layout s (fuel+3) "Q"
      (.aggregate [SignedValues.value mag neg,.natObject den])=some (rational mag neg den) := by
  exact TypedFrames.cast_aggregate Header.layout s (fuel+2) "Q" "Q"
    [("num","S"),("den","N")] [SignedValues.value mag neg,.natObject den]
    [SignedValues.value mag neg,.natObject den]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) rfl
    (rational_fields s fuel mag n neg den d magLive denLive bound)

end ScopedC.RecordCasts
