/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTInputLoaderModel
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.InputLoader
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings

inductive Profile where | fap | w4 deriving DecidableEq

def Profile.count : Profile → Nat | .fap=>400 | .w4=>2520
def Profile.grid : Profile → Nat | .fap=>131072 | .w4=>16777216
def Profile.encoded : Profile → Nat → Nat
  | .fap=> RH080Next.FapPV.Data.encodedNode
  | .w4=> RH080Next.WindowPV.Data.encodedNode

def Profile.program : Profile → Program
  | .fap=> FapFFTRecursivePV.program
  | .w4=> FFTRecursivePV.program

theorem Profile.shape (p : Profile) : 0< p.count ∧ 2*p.count< p.grid ∧ 12*p.grid<2^64:=by
  cases p <;> decide

theorem Profile.encoded_bound (p : Profile) (j : Nat) (hj : j< p.count) : p.encoded j<2*InputCell.scale:=by
  cases p with
  | fap=> exact RH080Next.FapPV.Data.encoded_fit ⟨j,hj⟩
  | w4=> exact RH080Next.WindowPV.Data.encoded_fit ⟨j,hj⟩

theorem Profile.lookup_correct {F : Type} (p : Profile) (context : Context F) (pinned : context.program=p.program)
    (before : State F) (j : Nat) (well : WellScoped before) (fits : j<2^64) : EncodedSelector.Correct context before j (p.encoded j):=by
  cases p with
  | fap=> exact (EncodedSelector.fap_encoded_node_correct context pinned before j well fits).2
  | w4=> exact (EncodedSelector.w4_encoded_node_correct context pinned before j well fits).2

structure Input where
  profile : Profile
  object : Nat

def parameterType : Parameter → CType | .data=>.pointer .u64 | _=>.u64

def parameterValues (input : Input) (j : Nat) : Parameter → Value
  | .data=>.pointer (wordPointer input.object 0)
  | .n=>.integer (integer64 input.profile.grid)
  | .j=>.integer (integer64 j)

structure LoopView {F : Type} (state : State F) (input : Input) (owner : Nat) (ids : Parameter → Nat) (j : Nat) : Prop where
  array : WordArrayRep state input.object (12*input.profile.grid) (currentData input.profile.encoded input.profile.grid j)
  locals : Locals state parameterName parameterType ids owner (parameterValues input j)
  separate : ∀p,input.object≠ids p
  active : j≤ input.profile.count
  well : WellScoped state

def initialIds (params : Parameter → Nat) : Var → Nat | .inl p=> params p | .inr _=>0

def initialValues (input : Input) (j : Nat) : Var → Value | .inl p=> parameterValues input j p | .inr _=>.integer (integer64 0)

/-- Entering the actual loader-body block does not assume any of its future
locals. Only the three already-declared main variables are initially active. -/
theorem LoopView.enter {F : Type} {before : State F} {input : Input} {functionOwner j : Nat} {ids : Parameter → Nat}
    (h : LoopView before input functionOwner ids j) :
    PartialBindings before.enterScope 0 functionOwner before.nextScope (initialIds ids) (initialValues input j):=by
  refine ⟨?_,?_,?_,?_⟩
  · intro v hv;cases v with
    | inl p=> cases p with
      | data=> exact h.locals.lookup .data
      | n=> exact h.locals.lookup .n
      | j=> exact h.locals.lookup .j
    | inr t=> cases t <;> simp [Active,localIndex] at hv
  · intro v hv;cases v with
    | inl p=> cases p with
      | data=> exact ⟨(h.locals.slots .data).storable,(h.locals.slots .data).object⟩
      | n=> exact ⟨(h.locals.slots .n).storable,(h.locals.slots .n).object⟩
      | j=> exact ⟨(h.locals.slots .j).storable,(h.locals.slots .j).object⟩
    | inr t=> cases t <;> simp [Active,localIndex] at hv
  · intro a b ha hb same
    cases a with
    | inl a=> cases b with
      | inl b=> exact congrArg Sum.inl (h.locals.distinct same)
      | inr b=> cases b <;> simp [Active,localIndex] at hb
    | inr a=> cases a <;> simp [Active,localIndex] at ha
  · intro v hv;cases v with
    | inl p=> have b:=h.locals.bound;change functionOwner< before.nextScope+1;omega
    | inr t=> cases t <;> simp [Active,localIndex] at hv

#print axioms Profile.lookup_correct
#print axioms LoopView.enter
end RH080Next.FFTPV.InputLoader
