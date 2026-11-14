/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedC.PositiveCasts
import ScopedC.DeclarationReturn

namespace ScopedC.SignedValues
open ScopedC.Syntax ScopedC.Machine ScopedC.SourceCalls ScopedC.PoolCalls ScopedC.NatWrapperCalls
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def value (slot neg : Nat) : Value := .record "S" [.natObject slot,unsigned32 neg]


theorem cast_fields {s : State} {slot n neg : Nat} (live : NatArena.Borrow s.nats slot n)
    (bound : neg < 2^32) :
    ([("mag","N"),("neg","unsigned")].zip [.natObject slot,unsigned32 neg]).mapM
      (fun item => castValue Header.layout s 99 item.1.2 item.2) =
      some [.natObject slot,unsigned32 neg] := by
  exact PositiveCasts.fields live bound

theorem cast_record {s : State} {slot n neg : Nat} (type : String)
    (normalize : normalizeType type = "S")
    (live : NatArena.Borrow s.nats slot n) (bound : neg < 2^32) :
    castValue Header.layout s 100 type (value slot neg) = some (value slot neg) := by
  apply TypedFrames.cast_record Header.layout s 99 type "S"
    [("mag","N"),("neg","unsigned")] [.natObject slot,unsigned32 neg] [.natObject slot,unsigned32 neg]
    normalize (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) rfl (cast_fields live bound)


theorem cast_aggregate {s : State} {slot n neg : Nat}
    (live : NatArena.Borrow s.nats slot n) (bound : neg < 2^32) :
    castValue Header.layout s 100 "S" (.aggregate [.natObject slot,unsigned32 neg]) = some (value slot neg) := by
  apply TypedFrames.cast_aggregate Header.layout s 99 "S" "S"
    [("mag","N"),("neg","unsigned")] [.natObject slot,unsigned32 neg] [.natObject slot,unsigned32 neg]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) rfl (cast_fields live bound)


theorem initialized (slot neg : Nat) : Machine.initialized 1000 (value slot neg) = true := by rfl

end ScopedC.SignedValues
