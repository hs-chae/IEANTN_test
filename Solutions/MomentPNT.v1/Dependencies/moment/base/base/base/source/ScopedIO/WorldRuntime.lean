/- Additive standard-I/O world, separate from the application's C memory.
Actual application globals and pointer addresses are unchanged. Standard
stdout is a platform handle, not an assumed application heap object. -/
import ScopedIO.Stream
namespace ScopedIO.WorldIO
open ScopedC ScopedC.Machine
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

structure World where
  app : State
  stream : Stream

structure Platform where
  stdoutAddress : Address

/-- Only the opaque standard C stdout handle. The application never
inspects its object representation or dereferences this platform pointer. -/
def stdoutValue (p : Platform) : Value := .pointer p.stdoutAddress true

def isStdout (p : Platform) : Value → Bool
  | .pointer a _ => a == p.stdoutAddress
  | _ => false

abbrev Call := String → List Value → World → Option (Value × World)

structure FaultPolicy where
  succeed : String → World → Bool
  count : String → World → Nat

def unsigned64 (n : Nat) : Value := .integer ⟨⟨false,64⟩,(n:ℤ)⟩
def signed32 (n : Int) : Value := .integer ⟨⟨true,32⟩,n⟩

/-- C prototype conversion of nonnegative, representable size arguments.
No arbitrary untyped or out-of-range application value is accepted. -/
def sizeArgument : Value → Option Nat
  | .integer v => if Scalar.InRange v.type v.number ∧ 0≤v.number ∧ v.number<2^64
      then some v.number.toNat else none
  | _ => none

/-- Exact typed read from an application-owned uint64_t array. A later
application proof must establish allocation, bounds, initialization and type. -/
def readWord64 (s : State) (a : Address) : Option Nat := do
  if !a.fields.isEmpty then none else
  let obj ← s.heap[a.object]?
  if obj.type != "uint64_t" || !obj.isArray then none else
  let some (.integer v) ← obj.cells[a.index]? | none
  if v.type=⟨false,64⟩ ∧ 0≤v.number ∧ v.number<2^64 then some v.number.toNat else none

/-- Documented little-endian uint64_t memory ABI. This is a generic platform
contract, not a statement that an application computed the correct words. -/
def wordBytes (n : Nat) : List Nat :=
  (List.range 8).map (fun j=>(n / 2^(8*j))%256)

def bufferBytes (s : State) (a : Address) : Option (List Nat) := do
  let words ← (List.range 8).mapM (fun i=>readWord64 s {a with index:=a.index+i})
  pure (words.flatMap wordBytes)

/-- Generic restricted fwrite case used by the source: eight objects of
size eight. Failure and partial acceptance are retained. A return count of
8, which the application must test, is the documented complete-write case. -/
def stdio (p : Platform) (fault : FaultPolicy) : Call := fun name args w => do
  if name="fwrite" then
    let [.pointer a _,size,count,handle] := args | none
    let size ← sizeArgument size
    let count ← sizeArgument count
    if size≠8 ∨ count≠8 ∨ !isStdout p handle then none else
    let bytes ← bufferBytes w.app a
    let ok := fault.succeed name w
    let accepted := fault.count name w
    pure (unsigned64 (if ok then 8 else min (accepted/8) 7),
      {w with stream:=writeBytes w.stream bytes ok accepted})
  else if name="fflush" then
    let [handle] := args | none
    if !isStdout p handle then none else
    let ok := fault.succeed name w
    pure (signed32 (if ok then 0 else -1),
      {w with stream:=flush w.stream ok (fault.count name w)})
  else none

/-- The unchanged core runtime plus standard-I/O only. No numerical,
application-initialization, success, or correct-output oracle is a leaf. -/
def external (p : Platform) (fault : FaultPolicy) : Call := fun name args w =>
  match RuntimeCore.call name args w.app with
  | some (v,t) => some (v,{w with app:=t})
  | none => stdio p fault name args w

theorem stdout_handle (p : Platform) : isStdout p (stdoutValue p)=true := by
  simp [isStdout,stdoutValue]

theorem runtime_included (p : Platform) (fault : FaultPolicy)
    {name : String} {args : List Value} {s t : State} {v : Value}
    (h : RuntimeCore.call name args s=some (v,t)) (stream : Stream) :
    external p fault name args ⟨s,stream⟩=some (v,⟨t,stream⟩) := by
  simp [external,h]

theorem wordBytes_length (n : Nat) : (wordBytes n).length=8 := by
  simp [wordBytes]

theorem wordBytes_valid (n : Nat) : ∀ b∈wordBytes n,b<256 := by
  intro b hb
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp hb
  exact Nat.mod_lt _ (by decide)

theorem no_application_leaves (p : Platform) (fault : FaultPolicy)
    (args : List Value) (w : World) :
    external p fault "pointHeight" args w=none ∧
    external p fault "pointEdge" args w=none ∧
    external p fault "main" args w=none := by
  simp [external,RuntimeCore.call,RuntimeCore.binaryName,stdio]

#print axioms runtime_included
#print axioms wordBytes_valid
#print axioms no_application_leaves
end ScopedIO.WorldIO
