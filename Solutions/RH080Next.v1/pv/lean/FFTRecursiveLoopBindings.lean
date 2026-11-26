/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTRecursiveBodyAST
import FFTRecursiveSourceLayout
import FFTProductBindings
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.RecursiveSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings ProductInner

inductive Buffer where | output | input | twiddle | work deriving DecidableEq

/-- Four actual main allocations, with the source's complete word extents.
The source recursion reuses disjoint output slices and one real work buffer. -/
structure Buffers (total : Nat) where
  object : Buffer → Nat
  length : Buffer → Nat
  distinct : Function.Injective object
  outputBound : 12*total ≤ length .output
  inputBound : 12*total ≤ length .input
  twiddleBound : 6*total ≤ length .twiddle
  workBound : 512 ≤ length .work

inductive LocalVar where | half | status | stride | j | temp deriving DecidableEq
abbrev LoopVar := Sum Var LocalVar

def localName : LocalVar → String
  | .half => "half" | .status => "status" | .stride => "stride" | .j => "j" | .temp => "temp"
def localType : LocalVar → CType
  | .temp => .pointer .u64 | _ => .u64

def loopName : LoopVar → String := Sum.elim name localName
def loopType : LoopVar → CType := Sum.elim type localType

def loopValue {total : Nat} (buffers : Buffers total) (start index step n j : Nat) : LoopVar → Value :=
  Sum.elim (value (buffers.object .output) (buffers.object .input) (buffers.object .twiddle)
      (buffers.object .work) start index step n total)
    (fun v => match v with
      | .half => .integer (integer64 (n/2))
      | .status => .integer (integer64 0)
      | .stride => .integer (integer64 (total/n))
      | .j => .integer (integer64 j)
      | .temp => .pointer (wordPointer (buffers.object .work) 160))

def bufferData (input table output work : Nat → Nat) : Buffer → Nat → Nat
  | .output => output | .input => input | .twiddle => table | .work => work

/-- All source-visible loop variables are real typed automatic objects; array
representations describe actual current buffers. No desired output is included. -/
structure LoopView {F : Type} (state : State F) {total : Nat} (buffers : Buffers total)
    (start index step n : Nat) (ids : LoopVar → Nat) (owner j : Nat)
    (input table output work : Nat → Nat) : Prop where
  bindings : Bindings state loopName loopType ids (fun _ => owner)
    (loopValue buffers start index step n j)
  arrays : ∀r, WordArrayRep state (buffers.object r) (buffers.length r)
    (bufferData input table output work r)
  well : WellScoped state
  active : j ≤ n/2

/-- Source parameters can be recovered without assuming another initialization
or altering the actual caller's mixed pointer/scalar storage. -/
theorem LoopView.parameters {F : Type} {state : State F} {total : Nat} {buffers : Buffers total}
    {start index step n : Nat} {ids : LoopVar → Nat} {owner j : Nat}
    {input table output work : Nat → Nat}
    (h : LoopView state buffers start index step n ids owner j input table output work) :
    Locals state name type (ids ∘ Sum.inl) owner
      (value (buffers.object .output) (buffers.object .input) (buffers.object .twiddle)
        (buffers.object .work) start index step n total) :=
  ⟨fun v => h.bindings.lookup (.inl v),fun v => h.bindings.slots (.inl v),
    h.bindings.distinct.comp Sum.inl_injective,h.bindings.bound (.inl .output)⟩

#print axioms LoopView.parameters
end RH080Next.FFTPV.RecursiveSource
