/- Actual original printS parameter binding and declarations, in source
order. The sign output lies between count and x declarations and is proved
separately in the stdio world. No initial application frame is assumed. -/
import ScopedIO.PrintSGeneration
import ScopedC.SignedValues

namespace ScopedIO.PrintSEntry
open ScopedC ScopedC.Syntax ScopedC.Machine ScopedC.SourceCalls ScopedC.PoolCalls
open ScopedC.NatWrapperCalls ScopedIO.PrintSFrames
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 100000

def beforeSign (s : State) (a : Value) : State :=
  allocate (buffer s a []) "unsigned int" "count" (some (unsigned32 0))

def withX (s : State) (a : Value) (slot : Nat) : State :=
  allocate (beforeSign s a) "N" "x" (some (.natObject slot))

theorem arguments {s : State} {slot n neg : Nat}
    (live : NatArena.Borrow s.nats slot n) (bound : neg < 2^32) :
    bindArgs Header.layout Generated.f_printS.parameters [SignedValues.value slot neg] s =
      some (parameter s (SignedValues.value slot neg)) :=
  TypedFrames.bind_one Header.layout s "S" "a" _ _
    (SignedValues.cast_record "S" rfl live bound)

theorem count_declaration (service : Call) (s : State) (a : Value) :
    declarations Header.layout service
      [{type:="unsigned int",name:="count",value:=some (.nat 0),arrayExtent:=none}]
      (buffer s a []) = some (beforeSign s a) := by
  rfl

theorem a_at (s : State) (slot neg : Nat) :
    LocalBinding.At (beforeSign s (SignedValues.value slot neg)) "a" "S"
      (SignedValues.value slot neg) s.heap.length := by
  constructor
  · simp [beforeSign,buffer,parameter,allocate,List.lookup]
  · simp [beforeSign,buffer,parameter,allocate,List.getElem?_append]
  · exact SignedValues.initialized _ _

theorem negative_expression (service : Call) (fuel : Nat) (s : State) (slot neg : Nat) :
    evalExpr Header.layout service (fuel+2) (beforeSign s (SignedValues.value slot neg))
      (.field "." (.var "a") "neg") =
      some (unsigned32 neg,beforeSign s (SignedValues.value slot neg)) := by
  apply ExpressionTemplates.field Header.layout service
    (LocalBinding.eval service fuel (a_at s slot neg)
      (by decide) (by decide) (by decide) (by decide))
  rfl

theorem magnitude_expression (service : Call) (fuel : Nat) (s : State) (slot neg : Nat) :
    evalExpr Header.layout service (fuel+2) (beforeSign s (SignedValues.value slot neg))
      (.field "." (.var "a") "mag") =
      some (.natObject slot,beforeSign s (SignedValues.value slot neg)) := by
  apply ExpressionTemplates.field Header.layout service
    (LocalBinding.eval service fuel (a_at s slot neg)
      (by decide) (by decide) (by decide) (by decide))
  rfl

theorem x_declaration (service : Call) {s : State} {slot n neg : Nat}
    (live : NatArena.Borrow s.nats slot n) :
    declarations Header.layout service
      [{type:="N",name:="x",value:=some (.field "." (.var "a") "mag"),arrayExtent:=none}]
      (beforeSign s (SignedValues.value slot neg)) =
      some (withX s (SignedValues.value slot neg) slot) := by
  have expression := magnitude_expression service 998 s slot neg
  have convert : castValue Header.layout (beforeSign s (SignedValues.value slot neg))
      100 "N" (.natObject slot) = some (.natObject slot) := PrimitiveCalls.cast_N live
  simp [declarations,List.foldlM,expression,convert,withX]

theorem first_declaration (service : Call) (s : State) (a : Value) (slot : Nat) :
    declarations Header.layout service
      [{type:="unsigned int",name:="first",value:=some (.nat 1),arrayExtent:=none}]
      (withX s a slot) = some (frame s a [] slot 0 1) := by
  rfl

theorem pop_body {s t : State} (a : Value) (ds : List Nat) (slot count first : Nat)
    (extent : t.heap.length = s.heap.length) :
    popScope (parameter s a) (frame t a ds slot count first) = parameter t a := by
  simp [popScope,frame,buffer,parameter,allocate,extent,List.take_append]

theorem pop_call {s t : State} (a : Value)
    (extent : t.heap.length = s.heap.length) (environment : t.env=s.env) :
    popScope s (parameter t a) = t :=
  OneFrames.pop_frame "S" "a" a extent environment

end ScopedIO.PrintSEntry
