/- Copyright (c) 2026 IEANTN contributors. Apache-2.0. -/
import SynergyC.ZeroBody
import ScopedC.TypedFrames
import ScopedC.ExpressionTemplates

namespace SynergyC.IntervalValues
open ScopedC ScopedC.Syntax ScopedC.Machine ScopedC.SourceCalls
open SynergyC.Word512 SynergyC.ZeroBody
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Same `I` record as the actual source. Bounds are application invariants,
not assumed computed outputs. -/
theorem cast_fields (s : State) (fuel : Nat) {lo hi : Int}
    (hl : Range lo) (hh : Range hi) :
    ([("lo","U"),("hi","U")].zip [value lo,value hi]).mapM
      (fun item => castValue Header.layout s (fuel+1) item.1.2 item.2) =
      some [value lo,value hi] := by
  change (do
    let x ← castValue Header.layout s (fuel+1) "U" (value lo)
    let y ← castValue Header.layout s (fuel+1) "U" (value hi)
    pure [x,y]) = _
  rw [cast_word_positive _ _ hl,cast_word_positive _ _ hh]
  rfl

theorem cast_record (s : State) (fuel : Nat) {lo hi : Int}
    (hl : Range lo) (hh : Range hi) :
    castValue Header.layout s (fuel+2) "I" (interval lo hi) = some (interval lo hi) := by
  exact TypedFrames.cast_record Header.layout s (fuel+1) "I" "I"
    [("lo","U"),("hi","U")] [value lo,value hi] [value lo,value hi]
    rfl rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) rfl (cast_fields s fuel hl hh)

theorem cast_aggregate (s : State) (fuel : Nat) {lo hi : Int}
    (hl : Range lo) (hh : Range hi) :
    castValue Header.layout s (fuel+2) "I" (.aggregate [value lo,value hi]) =
      some (interval lo hi) := by
  exact TypedFrames.cast_aggregate Header.layout s (fuel+1) "I" "I"
    [("lo","U"),("hi","U")] [value lo,value hi] [value lo,value hi]
    rfl rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) rfl (cast_fields s fuel hl hh)

theorem initialized_interval (lo hi : Int) : initialized 1000 (interval lo hi) = true := by
  rfl

theorem lo_field (lo hi : Int) : nested Header.layout (interval lo hi) ["lo"] = some (value lo) := by
  rfl

theorem hi_field (lo hi : Int) : nested Header.layout (interval lo hi) ["hi"] = some (value hi) := by
  rfl

def frame (s : State) (al ah bl bh : Int) : State :=
  allocate (allocate {s with env:=[]} "I" "a" (some (interval al ah)))
    "I" "b" (some (interval bl bh))

theorem bind (s : State) {al ah bl bh : Int}
    (hal : Range al) (hah : Range ah) (hbl : Range bl) (hbh : Range bh) :
    bindArgs Header.layout [("I","a"),("I","b")]
      [interval al ah,interval bl bh] s = some (frame s al ah bl bh) :=
  TypedFrames.bind_two Header.layout s "I" "a" "I" "b"
    (interval al ah) (interval bl bh) (interval al ah) (interval bl bh)
    (cast_record _ 98 hal hah) (cast_record _ 98 hbl hbh)

theorem eval_a (service : Call) (fuel : Nat) (s : State) (al ah bl bh : Int) :
    evalExpr Header.layout service (fuel+1) (frame s al ah bl bh) (.var "a") =
      some (interval al ah,frame s al ah bl bh) := by
  simp [evalExpr,getVar,frame,allocate,List.lookup,List.getElem?_append,
    Machine.read,nested,initialized,interval,value]

theorem eval_b (service : Call) (fuel : Nat) (s : State) (al ah bl bh : Int) :
    evalExpr Header.layout service (fuel+1) (frame s al ah bl bh) (.var "b") =
      some (interval bl bh,frame s al ah bl bh) := by
  simp [evalExpr,getVar,frame,allocate,List.lookup,List.getElem?_append,
    Machine.read,nested,initialized,interval,value]

theorem eval_a_lo (service : Call) (fuel : Nat) (s : State) (al ah bl bh : Int) :
    evalExpr Header.layout service (fuel+2) (frame s al ah bl bh)
      (.field "." (.var "a") "lo") = some (value al,frame s al ah bl bh) :=
  ExpressionTemplates.field Header.layout service (eval_a service fuel s al ah bl bh) (lo_field al ah)

theorem eval_a_hi (service : Call) (fuel : Nat) (s : State) (al ah bl bh : Int) :
    evalExpr Header.layout service (fuel+2) (frame s al ah bl bh)
      (.field "." (.var "a") "hi") = some (value ah,frame s al ah bl bh) :=
  ExpressionTemplates.field Header.layout service (eval_a service fuel s al ah bl bh) (hi_field al ah)

theorem eval_b_lo (service : Call) (fuel : Nat) (s : State) (al ah bl bh : Int) :
    evalExpr Header.layout service (fuel+2) (frame s al ah bl bh)
      (.field "." (.var "b") "lo") = some (value bl,frame s al ah bl bh) :=
  ExpressionTemplates.field Header.layout service (eval_b service fuel s al ah bl bh) (lo_field bl bh)

theorem eval_b_hi (service : Call) (fuel : Nat) (s : State) (al ah bl bh : Int) :
    evalExpr Header.layout service (fuel+2) (frame s al ah bl bh)
      (.field "." (.var "b") "hi") = some (value bh,frame s al ah bl bh) :=
  ExpressionTemplates.field Header.layout service (eval_b service fuel s al ah bl bh) (hi_field bl bh)

theorem pop_frame (s : State) (al ah bl bh : Int) :
    popScope s (frame s al ah bl bh) = s := by simp [popScope,frame,allocate,List.take_append]

end SynergyC.IntervalValues
