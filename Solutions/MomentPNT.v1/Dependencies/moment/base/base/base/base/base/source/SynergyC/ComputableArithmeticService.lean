/- Copyright (c) 2026 IEANTN contributors. Apache-2.0. -/
import SynergyC.ArithmeticService
import ScopedC.ArrayLegacyLift

namespace SynergyC.ComputableArithmeticService
open ScopedC ScopedC.Syntax ScopedC.Machine
open SynergyC.Word512 SynergyC.WordFrames
open SynergyC.ArithmeticService (Operation)
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

local instance (n : Int) : Decidable (Range n) := by
  unfold Range
  infer_instance

/-- Construct the application-state precondition by inspecting the actual
global lookup, allocated scalar object and stored typed word. No prepared
application state, numerical output or successful effect is assumed. -/
def maxContext? (s : State) : Option (MaxContext s) :=
  match located : s.globals.lookup "MAXU" with
  | none => none
  | some address =>
    match heapEntry : s.heap[address.object]? with
    | none => none
    | some object =>
      if scalar : object.isArray = false then
        match contents : read Header.layout s address with
        | some (.integer v) =>
          if exactWord : v = word maxWord then
            some {
              address := address
              located := located
              allocated := (List.getElem?_eq_some_iff.mp heapEntry).choose
              object := object
              heap_entry := heapEntry
              scalar := scalar
              contents := by simpa only [exactWord,Word512.value] using contents }
          else none
        | _ => none
      else none

/-- The guards are ordinary decidable integer comparisons. In particular,
neither Nonempty MaxContext nor a classical decision procedure is executed. -/
def check (op : Operation) (a b : Int) : Bool :=
  decide (Range a) && decide (Range b) &&
    match op with
    | .add | .mul => decide (Range (ArithmeticService.result op a b))
    | .ceil => decide (0 < b)

theorem check_sound {op : Operation} {s : State} (ctx : MaxContext s)
    {a b : Int} (h : check op a b = true) :
    ArithmeticService.permitted op s a b := by
  cases op <;> simp only [check,Bool.and_eq_true,decide_eq_true_eq] at h
  all_goals exact ⟨h.1.1,h.1.2,⟨ctx⟩,h.2⟩

/-- A computable summary of the three actual C arithmetic bodies. Its
successful answers will be proved source calls of those same installed bodies;
this is not an independent numerical VM or a supplied-output checker. -/
def call : Call := fun called args s => do
  let op ← ArithmeticService.operation called
  let [.integer a,.integer b] := args | none
  let _ ← maxContext? s
  if check op a.number b.number then
    some (value (ArithmeticService.result op a.number b.number),s)
  else none

/-- Each successful computable summary is already covered by the proof-only
service, which in turn executes the actual parsed C bodies. -/
theorem refines {called : String} {args : List Value} {s t : State} {v : Value}
    (h : call called args s = some (v,t)) :
    ArithmeticService.call called args s = some (v,t) := by
  unfold call at h
  cases ho : ArithmeticService.operation called with
  | none => simp [ho] at h
  | some op =>
    simp only [ho,Bind.bind,Option.bind] at h
    split at h
    · rename_i a b
      cases hc : maxContext? s with
      | none => simp [hc] at h
      | some ctx =>
        simp only [hc,Option.bind_some] at h
        split_ifs at h with good
        · have hn := ArithmeticService.operation_name ho
          have accepted := ArithmeticService.complete a b (check_sound ctx good)
          simp only [Option.some.injEq,Prod.mk.injEq] at h
          rcases h with ⟨rfl,rfl⟩
          simpa only [← hn] using accepted
    · contradiction

theorem closed (code : List Function)
    (addInstalled : Generated.f_addU ∈ code) (mulInstalled : Generated.f_mulU ∈ code)
    (ceilInstalled : Generated.f_ceilDiv ∈ code)
    (checked : ArithmeticService.parameters code = true)
    {called : String} {args : List Value} {s t : State} {v : Value}
    (h : call called args s = some (v,t)) :
    SourceCalls.SourceCall Header.layout code 2 called args s v t :=
  ArithmeticService.closed code addInstalled mulInstalled ceilInstalled checked (refines h)

/-- The same full states, inputs, result, function source and ABI boundary
are retained in the additive initialized-array execution model. -/
theorem array_closed (code : List Function)
    (addInstalled : Generated.f_addU ∈ code) (mulInstalled : Generated.f_mulU ∈ code)
    (ceilInstalled : Generated.f_ceilDiv ∈ code)
    (checked : ArithmeticService.parameters code = true)
    {called : String} {args : List Value} {s t : State} {v : Value}
    (h : call called args s = some (v,t)) :
    ArraySourceCalls.SourceCall Header.layout code 2 called args s v t :=
  ArrayLegacyLift.source_call (closed code addInstalled mulInstalled ceilInstalled checked h)

end SynergyC.ComputableArithmeticService
