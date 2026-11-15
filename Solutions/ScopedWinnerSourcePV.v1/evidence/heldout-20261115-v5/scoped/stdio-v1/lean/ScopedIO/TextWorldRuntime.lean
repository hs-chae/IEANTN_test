/- Additive text stdio contracts for the original Scoped Winner program.
The stream remains separate from application memory. Original -100 formats
are retained; these are not the later height program's binary -128 output. -/
import ScopedIO.WorldRuntime
import ScopedIO.Runtime

namespace ScopedIO.TextWorldIO
open ScopedC ScopedC.Machine ScopedIO.WorldIO
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- The prototype accepts only a well-typed value representable as C int.
The unsigned-char conversion, including negative int arguments, is explicit. -/
def characterArgument : Value → Option Nat
  | .integer c =>
    if Scalar.InRange c.type c.number ∧ Scalar.InRange ⟨true,32⟩ c.number
    then some (c.number % 256).toNat else none
  | _ => none

/-- Only documented putchar/printf contracts are added. The two printf
formats are parsed from actual initialized application memory by printfBytes.
Partial acceptance and errors remain possible; printS ignores putchar's
return value, so successful program termination does not prove successful I/O. -/
def stdio (p : WorldIO.Platform) (fault : WorldIO.FaultPolicy) : WorldIO.Call :=
    fun name args w => do
  if name = "putchar" then
    let [arg] := args | none
    let byte ← characterArgument arg
    let ok := fault.succeed name w
    pure (signed32 (if ok then byte else -1),
      {w with stream := writeBytes w.stream [byte] ok (fault.count name w)})
  else if name = "printf" then
    let bytes ← ScopedIO.printfBytes args w.app
    if bytes.length < 2^31 then
      let ok := fault.succeed name w
      pure (signed32 (if ok then bytes.length else -1),
        {w with stream := writeBytes w.stream bytes ok (fault.count name w)})
    else none
  else WorldIO.stdio p fault name args w

/-- Existing generic core runtime plus text/binary stdio; no application
initialization, intended output, or application numerical function is a leaf. -/
def external (p : WorldIO.Platform) (fault : WorldIO.FaultPolicy) : WorldIO.Call :=
    fun name args w =>
  match RuntimeCore.call name args w.app with
  | some (v,t) => some (v,{w with app := t})
  | none => stdio p fault name args w

theorem characterArgument_valid {arg : Value} {byte : Nat}
    (h : characterArgument arg = some byte) : byte < 256 := by
  cases arg with
  | integer c =>
    simp only [characterArgument] at h
    split at h
    next range =>
      have value : (c.number % 256).toNat = byte := Option.some.inj h
      rw [← value]
      exact Int.toNat_lt (Int.emod_nonneg _ (by decide)) |>.mpr
        (Int.emod_lt_of_pos _ (by decide))
    next impossible => contradiction
  | _ => contradiction

theorem runtime_included (p : WorldIO.Platform) (fault : WorldIO.FaultPolicy)
    {name : String} {args : List Value} {s t : State} {v : Value}
    (h : RuntimeCore.call name args s = some (v,t)) (stream : Stream) :
    external p fault name args ⟨s,stream⟩ = some (v,⟨t,stream⟩) := by
  simp [external,h]

theorem putchar_result (p : WorldIO.Platform) (fault : WorldIO.FaultPolicy)
    {arg : Value} {byte : Nat} (h : characterArgument arg = some byte) (w : World) :
    stdio p fault "putchar" [arg] w =
      some (signed32 (if fault.succeed "putchar" w then byte else -1),
        {w with stream := (writeBytes w.stream [byte]
          (fault.succeed "putchar" w) (fault.count "putchar" w))}) := by
  simp [stdio,h]

theorem printf_result (p : WorldIO.Platform) (fault : WorldIO.FaultPolicy)
    {args : List Value} {bytes : List Nat} (w : World)
    (h : ScopedIO.printfBytes args w.app = some bytes) (small : bytes.length < 2^31) :
    stdio p fault "printf" args w =
      some (signed32 (if fault.succeed "printf" w then bytes.length else -1),
        {w with stream := (writeBytes w.stream bytes
          (fault.succeed "printf" w) (fault.count "printf" w))}) := by
  have small' : bytes.length < 2147483648 := small
  simp [stdio,h,small']

theorem no_application_leaves (p : WorldIO.Platform) (fault : WorldIO.FaultPolicy)
    (args : List Value) (w : World) :
    external p fault "printS" args w = none ∧
    external p fault "printI" args w = none ∧
    external p fault "evaluate" args w = none ∧
    external p fault "runRow" args w = none ∧
    external p fault "main" args w = none := by
  simp [external,RuntimeCore.call,RuntimeCore.binaryName,stdio,WorldIO.stdio]

end ScopedIO.TextWorldIO
