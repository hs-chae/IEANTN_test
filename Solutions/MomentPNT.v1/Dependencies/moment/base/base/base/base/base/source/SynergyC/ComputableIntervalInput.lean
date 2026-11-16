/- Copyright (c) 2026 IEANTN contributors. Apache-2.0. -/
import SynergyC.ComputableArithmeticService
import SynergyC.UnitBody

namespace SynergyC.ComputableIntervalInput
open ScopedC ScopedC.Machine
open SynergyC.Word512
set_option autoImplicit false
set_option maxHeartbeats 100000

/-- Read and check the actual global scale storage. No initial application
representation, successful source effect or expected output is assumed. -/
def scaleContext? (s : State) : Option (UnitBody.ScaleContext s) :=
  match located : s.globals.lookup "S" with
  | none => none
  | some address =>
    match heapEntry : s.heap[address.object]? with
    | none => none
    | some object =>
      if scalar : object.isArray=false then
        match contents : read Header.layout s address with
        | some (.integer v) =>
          if exactWord : v=word (2^128) then
            some {
              address:=address
              located:=located
              allocated:=(List.getElem?_eq_some_iff.mp heapEntry).choose
              object:=object
              heap_entry:=heapEntry
              scalar:=scalar
              contents:=by simpa only[exactWord,Word512.value] using contents }
          else none
        | _ => none
      else none

structure Bounds where
  lo : Int
  hi : Int

/-- Decode the actual canonical two-word source record. The dependent
result proves its exact original Value identity. The decisions inspect only
the record tag and the two scalar types, with no general Value equality. -/
def interval? (v : Value) : Option {b : Bounds // v=ZeroBody.interval b.lo b.hi} :=
  match v with
  | .record tag [.integer lo,.integer hi] =>
    if tagEq : tag="I" then
      if loEq : lo.type=Word512.type then
        if hiEq : hi.type=Word512.type then
          some ⟨⟨lo.number,hi.number⟩,by
            cases lo
            cases hi
            cases loEq
            cases hiEq
            cases tagEq
            rfl⟩
        else none
      else none
    else none
  | _ => none

theorem interval_canonical (lo hi : Int) :
    (interval? (ZeroBody.interval lo hi)).map (fun x=>x.val)=some ⟨lo,hi⟩ := by
  rfl

end SynergyC.ComputableIntervalInput
