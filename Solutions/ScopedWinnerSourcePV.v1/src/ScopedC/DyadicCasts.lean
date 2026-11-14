/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedC.RecordCasts
import ScopedC.SignedNegBody

namespace ScopedC.DyadicCasts
open ScopedC.Machine ScopedC.NatWrapperCalls
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def value (lo hi : Value) (ok : Bool) : Value :=
  .record "I" [lo,hi,unsigned32 (SignedNegCalls.bit ok)]

theorem fields (s : State) (fuel : Nat) (lo hi : Value) (ok : Bool)
    (hl : castValue Header.layout s (fuel+2) "S" lo=some lo)
    (hh : castValue Header.layout s (fuel+2) "S" hi=some hi) :
    ([("lo","S"),("hi","S"),("ok","unsigned")].zip
      [lo,hi,unsigned32 (SignedNegCalls.bit ok)]).mapM
      (fun item => castValue Header.layout s (fuel+2) item.1.2 item.2)=
      some [lo,hi,unsigned32 (SignedNegCalls.bit ok)] := by
  change (do
    let x ← castValue Header.layout s (fuel+2) "S" lo
    let y ← castValue Header.layout s (fuel+2) "S" hi
    let z ← castValue Header.layout s (fuel+2) "unsigned" (unsigned32 (SignedNegCalls.bit ok))
    pure [x,y,z])=some [lo,hi,unsigned32 (SignedNegCalls.bit ok)]
  rw [hl,hh,PositiveCasts.cast_unsigned s (fuel+1) _ (SignedNegCalls.bit_bound ok)]
  rfl

theorem record (s : State) (fuel : Nat) (type : String)
    (normalize : normalizeType type="I") (lo hi : Value) (ok : Bool)
    (hl : castValue Header.layout s (fuel+2) "S" lo=some lo)
    (hh : castValue Header.layout s (fuel+2) "S" hi=some hi) :
    castValue Header.layout s (fuel+3) type (value lo hi ok)=some (value lo hi ok) := by
  exact TypedFrames.cast_record Header.layout s (fuel+2) type "I"
    [("lo","S"),("hi","S"),("ok","unsigned")]
    [lo,hi,unsigned32 (SignedNegCalls.bit ok)] [lo,hi,unsigned32 (SignedNegCalls.bit ok)] normalize
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) rfl (fields s fuel lo hi ok hl hh)

theorem aggregate (s : State) (fuel : Nat) (lo hi : Value) (ok : Bool)
    (hl : castValue Header.layout s (fuel+2) "S" lo=some lo)
    (hh : castValue Header.layout s (fuel+2) "S" hi=some hi) :
    castValue Header.layout s (fuel+3) "I" (.aggregate [lo,hi,unsigned32 (SignedNegCalls.bit ok)])=
      some (value lo hi ok) := by
  exact TypedFrames.cast_aggregate Header.layout s (fuel+2) "I" "I"
    [("lo","S"),("hi","S"),("ok","unsigned")]
    [lo,hi,unsigned32 (SignedNegCalls.bit ok)] [lo,hi,unsigned32 (SignedNegCalls.bit ok)]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) rfl (fields s fuel lo hi ok hl hh)

end ScopedC.DyadicCasts
