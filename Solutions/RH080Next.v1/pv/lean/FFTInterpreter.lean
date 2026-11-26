/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import GoldbachDirect.Interpreter
import FFTAST
import FFTWordArrays
import GoldbachDirect.PlatformMemory
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace RH080Next.FFTPV.Certified
open GoldbachDirect GoldbachDirect.Semantics

def context : Context Unit :=
  {program:=FFTPV.program,foreign:=fun _ _ _ _ _=>False,
   headerConstant:=fun _=>none,builtin:=fun _ _=>none}

/-- Numerical helpers have no foreign calls. Any unexpected external call fails
rather than receiving an application-correctness oracle. -/
def noForeign : Interpreter.PrimitiveExecutor context := fun _ _ _=>none

def rawScratch : State Unit :=
  {environment:=[],objects := fun object => if object=0 then some {extent:=4096,storage:=.host,cells:=PlatformMemory.zeroBytes 4096} else none,
   nextObject:=1,scope:=0,nextScope:=1,mode:=.host,foreign:=()}

def rootArgs : List Value := [.pointer (WordArrays.wordPointer 0 128),
  .integer (WordArrays.integer64 16777216),.pointer (WordArrays.wordPointer 0 0)]

def invokeRoot := Interpreter.invoke 10000 context noForeign "initialize_root" rootArgs rawScratch

def readRoot (state : State Unit) : Option (List Nat) :=
  (List.range 12).mapM fun j => do
    let value ← state.load (WordArrays.wordPointer 0 (128+j))
    match value with
    | .integer word => if word.kind == .u64 then some word.bits else none
    | _=>none

def rootResult : Option (List Nat) := do
  let out ← invokeRoot
  match out.val.1 with
  | .value (.integer status) =>
    let root ← readRoot out.val.2
    return status.bits::root
  | _=>none

/-- The core interpreter returns actual operational proofs of the same source
program and state. No trusted interpretation of an application name is used. -/
theorem invokeRoot_sound {out : Interpreter.Called context "initialize_root" rootArgs rawScratch}
    (h : invokeRoot=some out) :
    Call context "initialize_root" rootArgs rawScratch out.val.1 out.val.2 :=
  Interpreter.invoke_sound h

#print axioms invokeRoot_sound
end RH080Next.FFTPV.Certified
