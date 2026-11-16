/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import SynergyC.WordFrames
import SynergyC.BundleProjections
namespace SynergyC.Initialization
open ScopedC ScopedC.Machine
open SynergyC.Word512 SynergyC.WordFrames
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Static initialization in the selected type subset. Unlike automatic
locals, static storage is zero-initialized before its explicit initializer. -/
def zeroValue : Nat → String → Option Value
  | 0,_ => none
  | fuel+1,type => do
    let ty := normalizeType type
    if let some ti := Header.layout.integers.lookup ty then
      pure (.integer (←Scalar.checked ti 0))
    else
      let fs ← fieldsOf Header.layout ty
      let vals ← fs.mapM (fun f => zeroValue fuel f.2)
      pure (.record ty vals)

def initializeOne (st : State) (d : Syntax.Decl) : Option State := do
  if d.arrayExtent.isSome then none else
  let (v,next) ← match d.value with
    | some e => evalExpr Header.layout RuntimeCore.call 100 st e
    | none => do pure (←zeroValue 10 d.type,st)
  let w ← castValue Header.layout next 100 d.type v
  pure (allocate next d.type d.name (some w))

def initializeGlobals : Option State := do
  let st ← Header.globals.foldlM initializeOne Machine.empty
  pure {st with env:=[],globals:=st.env}

def state : State := {
  heap:=[
    {type:="const U",cells:=[some (value (2^128))]},
    {type:="const U",cells:=[some (value maxWord)]},
    {type:="I",cells:=[some (.record "I" [value 0,value 0])]}]
  env:=[]
  globals:=[("ln2",⟨2,0,[]⟩),("MAXU",⟨1,0,[]⟩),("S",⟨0,0,[]⟩)]
  nats:=NatArena.empty}

/-- This equation consumes the actual structured global declarations bound
by Bundle.globals_exact; it never assumes an initialized application heap. -/
theorem actual_initialization : initializeGlobals = some state := by
  rfl

def maxContext : MaxContext state := {
  address:=⟨1,0,[]⟩
  located:=by rfl
  allocated:=by decide +kernel
  object:={type:="const U",cells:=[some (value maxWord)]}
  heap_entry:=by rfl
  scalar:=by rfl
  contents:=by rfl}

#print axioms actual_initialization
#print axioms maxContext
end SynergyC.Initialization
