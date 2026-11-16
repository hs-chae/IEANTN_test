/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import ScopedC.Machine

namespace ScopedC.RuntimeCore
open ScopedC.Machine
set_option autoImplicit false
set_option maxHeartbeats 0

/-- Exactly the generic, pinned Nat ABI boundary. Application rational,
Taylor, interval, DAG and integration functions are deliberately absent. -/
def binaryName (name : String) : Option NatArena.BinaryOp :=
  if name == "lean_nat_add" then some .add
  else if name == "lean_nat_sub" then some .sub
  else if name == "lean_nat_mul" then some .mul
  else if name == "lean_nat_div" then some .div
  else if name == "lean_nat_mod" then some .mod
  else if name == "lean_nat_gcd" then some .gcd
  else if name == "lean_nat_shiftl" then some .shiftLeft
  else if name == "lean_nat_shiftr" then some .shiftRight
  else none

def result (st : State) (n : Nat) : Value × State :=
  let (slot,arena) := NatArena.allocate st.nats n
  (.natObject slot,{st with nats:=arena})

def unsignedResult (width n : Nat) (st : State) : Option (Value × State) := do
  let v ← Scalar.checked ⟨false,width⟩ (n : Int)
  pure (.integer v,st)

/-- The source-level contract of the pinned core runtime, not verification
of its implementation. Every Nat input must have an application-owned live
token. Result tokens need explicit registration/release in the C application.
Physical aliasing of boxed scalars/results is permitted by the reference
provenance abstraction; no pointer-uniqueness claim is used. -/
def call : Call := fun name args st => do
  if let some op := binaryName name then
    let [.natObject a,.natObject b] := args | none
    let (slot,arena) ← NatArena.binary op st.nats a b
    pure (.natObject slot,{st with nats:=arena})
  else if name == "lean_unsigned_to_nat" then
    let [.integer a] := args | none
    if 0 ≤ a.number ∧ a.number < 2^32 then pure (result st a.number.toNat) else none
  else if name == "lean_uint64_to_nat" then
    let [.integer a] := args | none
    if 0 ≤ a.number ∧ a.number < 2^64 then pure (result st a.number.toNat) else none
  else if name == "lean_nat_log2" then
    let [.natObject slot] := args | none
    let n ← NatArena.read st.nats slot
    pure (result st n.log2)
  else if name == "lean_nat_dec_eq" || name == "lean_nat_dec_le" || name == "lean_nat_dec_lt" then
    let [.natObject a,.natObject b] := args | none
    let x ← NatArena.read st.nats a
    let y ← NatArena.read st.nats b
    let p := if name == "lean_nat_dec_eq" then x == y
      else if name == "lean_nat_dec_le" then decide (x ≤ y) else decide (x < y)
    unsignedResult 8 (if p then 1 else 0) st
  else if name == "lean_unbox" then
    let [.natObject slot] := args | none
    let n ← NatArena.read st.nats slot
    -- Exact pinned 64-bit small-Nat applicability condition. Larger objects
    -- are rejected, even if an accidental raw pointer shift produced a value.
    if n < 2^63 then unsignedResult 64 n st else none
  else if name == "lean_inc" then
    let [.natObject slot] := args | none
    let arena ← NatArena.retain st.nats slot
    pure (.unit,{st with nats:=arena})
  else if name == "lean_dec" then
    let [.natObject slot] := args | none
    let arena ← NatArena.release st.nats slot
    pure (.unit,{st with nats:=arena})
  else if name == "lean_initialize_runtime_module" then
    let [] := args | none
    pure (.unit,st)
  else none

theorem no_application_evaluator (args : List Value) (st : State) :
    call "evaluate" args st = none := rfl

theorem no_rational_operation (args : List Value) (st : State) :
    call "qt" args st = none := rfl

theorem no_integration_program (args : List Value) (st : State) :
    call "runRow" args st = none := rfl

theorem constructed_result_live (st : State) (n : Nat) :
    NatArena.Borrow (result st n).2.nats st.nats.values.length n := by
  exact NatArena.allocate_borrow st.nats n

#print axioms no_application_evaluator
#print axioms constructed_result_live
end ScopedC.RuntimeCore
