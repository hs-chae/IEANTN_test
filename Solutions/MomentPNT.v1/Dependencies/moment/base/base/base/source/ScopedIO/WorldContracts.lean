/- Generic return-checked stdio properties, with the platform stream outside
application memory. Failure remains possible and is not a success premise. -/
import ScopedIO.WorldRuntime
namespace ScopedIO.WorldIO
open ScopedC ScopedC.Machine
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def integerNumber : Value → Int
  | .integer n => n.number
  | _ => 0

theorem fwrite_equation (p : Platform) (fault : FaultPolicy) (w : World)
    (a : Address) (writable : Bool) (size count handle : Value) (bytes : List Nat)
    (hs : sizeArgument size=some 8) (hc : sizeArgument count=some 8)
    (hh : isStdout p handle=true) (hb : bufferBytes w.app a=some bytes) :
    stdio p fault "fwrite" [.pointer a writable,size,count,handle] w=
      some (unsigned64 (if fault.succeed "fwrite" w then 8 else min (fault.count "fwrite" w/8) 7),
        {w with stream:=writeBytes w.stream bytes (fault.succeed "fwrite" w) (fault.count "fwrite" w)}) := by
  simp [stdio,hs,hc,hh,hb]

theorem fwrite_full (p : Platform) (fault : FaultPolicy) {w after : World}
    (a : Address) (writable : Bool) (size count handle : Value) (bytes : List Nat)
    (hs : sizeArgument size=some 8) (hc : sizeArgument count=some 8)
    (hh : isStdout p handle=true) (hb : bufferBytes w.app a=some bytes)
    (call : stdio p fault "fwrite" [.pointer a writable,size,count,handle] w=
      some (unsigned64 8,after)) :
    after.app=w.app ∧ after.stream.accepted=w.stream.accepted++bytes := by
  rw [fwrite_equation p fault w a writable size count handle bytes hs hc hh hb] at call
  have eq := Option.some.inj call
  have number := congrArg (fun v : Value × World=>integerNumber v.1) eq
  have state := congrArg Prod.snd eq
  cases ok : fault.succeed "fwrite" w
  · simp only [ok,Bool.false_eq_true,↓reduceIte,unsigned64,integerNumber] at number
    have bounded : min (fault.count "fwrite" w/8) 7 ≤ 7 := Nat.min_le_right _ _
    omega
  · simp only [ok,↓reduceIte] at state
    rw [←state]
    exact ⟨rfl,rfl⟩

theorem fflush_equation (p : Platform) (fault : FaultPolicy) (w : World) (handle : Value)
    (hh : isStdout p handle=true) :
    stdio p fault "fflush" [handle] w=
      some (signed32 (if fault.succeed "fflush" w then 0 else -1),
        {w with stream:=flush w.stream (fault.succeed "fflush" w) (fault.count "fflush" w)}) := by
  simp [stdio,hh]

theorem fflush_zero (p : Platform) (fault : FaultPolicy) {w after : World}
    (handle : Value) (hh : isStdout p handle=true)
    (call : stdio p fault "fflush" [handle] w=some (signed32 0,after)) :
    after.app=w.app ∧ after.stream.accepted=w.stream.accepted ∧
      after.stream.delivered=w.stream.accepted.length := by
  rw [fflush_equation p fault w handle hh] at call
  have eq := Option.some.inj call
  have number := congrArg (fun v : Value × World=>integerNumber v.1) eq
  have state := congrArg Prod.snd eq
  cases ok : fault.succeed "fflush" w
  · simp [ok,integerNumber,signed32] at number
  · simp only [ok,↓reduceIte] at state
    rw [←state]
    exact ⟨rfl,rfl,rfl⟩

#print axioms fwrite_equation
#print axioms fwrite_full
#print axioms fflush_equation
#print axioms fflush_zero
end ScopedIO.WorldIO
