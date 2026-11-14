/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedC.RecordCasts

namespace ScopedC.IntervalCasts
open ScopedC.Machine
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def value (lo hi : Value) : Value := .record "RI" [lo,hi]

theorem fields (s : State) (fuel : Nat) (lo hi : Value)
    (hl : castValue Header.layout s (fuel+3) "Q" lo=some lo)
    (hh : castValue Header.layout s (fuel+3) "Q" hi=some hi) :
    ([("lo","Q"),("hi","Q")].zip [lo,hi]).mapM
      (fun item => castValue Header.layout s (fuel+3) item.1.2 item.2)=some [lo,hi] := by
  change (do
    let x ← castValue Header.layout s (fuel+3) "Q" lo
    let y ← castValue Header.layout s (fuel+3) "Q" hi
    pure [x,y])=some [lo,hi]
  rw [hl,hh]
  rfl

theorem record (s : State) (fuel : Nat) (type : String)
    (normalize : normalizeType type="RI") (lo hi : Value)
    (hl : castValue Header.layout s (fuel+3) "Q" lo=some lo)
    (hh : castValue Header.layout s (fuel+3) "Q" hi=some hi) :
    castValue Header.layout s (fuel+4) type (value lo hi)=some (value lo hi) := by
  exact TypedFrames.cast_record Header.layout s (fuel+3) type "RI"
    [("lo","Q"),("hi","Q")] [lo,hi] [lo,hi] normalize
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) rfl (fields s fuel lo hi hl hh)

theorem aggregate (s : State) (fuel : Nat) (lo hi : Value)
    (hl : castValue Header.layout s (fuel+3) "Q" lo=some lo)
    (hh : castValue Header.layout s (fuel+3) "Q" hi=some hi) :
    castValue Header.layout s (fuel+4) "RI" (.aggregate [lo,hi])=some (value lo hi) := by
  exact TypedFrames.cast_aggregate Header.layout s (fuel+3) "RI" "RI"
    [("lo","Q"),("hi","Q")] [lo,hi] [lo,hi]
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) rfl (fields s fuel lo hi hl hh)

end ScopedC.IntervalCasts
