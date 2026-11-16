/- Copyright (c) 2026 IEANTN contributors. Apache-2.0. -/
import SynergyHeightC.Definitions
import SynergyC.Initialization
import SynergyC.UnitBody

namespace SynergyHeightC.Initialization
open ScopedC ScopedC.Machine
open SynergyC.Word512 SynergyC.WordFrames
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Static storage is initialized from the actual source declarations. The
array branch implements static zero initialization; no computed constants or
initial application representation are accepted as a platform assumption. -/
def initializeOne (st : State) (d : Syntax.Decl) : Option State := do
  match d.arrayExtent with
  | some extent =>
    if d.value.isSome then none else
    let zero ← SynergyC.Initialization.zeroValue 10 d.type
    pure {st with
      heap:=st.heap++[{type:=d.type,cells:=List.replicate extent (some zero),isArray:=true}]
      env:=(d.name,⟨st.heap.length,0,[]⟩)::st.env}
  | none => SynergyC.Initialization.initializeOne st d

def initializeGlobals : Option State := do
  let st ← Generated.globals.foldlM initializeOne Machine.empty
  pure {st with env:=[],globals:=st.env}

def zeroI : Value := .record "I" [value 0,value 0]
def state : State := {
  heap:=[
    {type:="const U",cells:=[some (value (2^128))]},
    {type:="const U",cells:=[some (value maxWord)]}]++
      List.replicate 11 {type:="I",cells:=[some zeroI]}++
      [{type:="I",cells:=List.replicate 58 (some zeroI),isArray:=true}]
  env:=[]
  globals:=[("constantNodes",⟨13,0,[]⟩),("smoothingBox",⟨12,0,[]⟩),
    ("deltaBox",⟨11,0,[]⟩),("dBox",⟨10,0,[]⟩),("alphaBox",⟨9,0,[]⟩),
    ("sqrt2Alpha",⟨8,0,[]⟩),("sqrtPi",⟨7,0,[]⟩),("peakBox",⟨6,0,[]⟩),
    ("gaussianBox",⟨5,0,[]⟩),("m0Box",⟨4,0,[]⟩),("piBox",⟨3,0,[]⟩),
    ("ln2",⟨2,0,[]⟩),("MAXU",⟨1,0,[]⟩),("S",⟨0,0,[]⟩)]
  nats:=NatArena.empty}

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

def scaleContext : SynergyC.UnitBody.ScaleContext state := {
  address:=⟨0,0,[]⟩
  located:=by rfl
  allocated:=by decide +kernel
  object:={type:="const U",cells:=[some (value (2^128))]}
  heap_entry:=by rfl
  scalar:=by rfl
  contents:=by rfl}

#print axioms actual_initialization
#print axioms maxContext
#print axioms scaleContext
end SynergyHeightC.Initialization
