/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedC.RationalUnsignedCall
import ScopedC.DyadicIntervalNegBody

namespace ScopedC.DyadicZeroCalls
open ScopedC.Syntax ScopedC.Machine ScopedC.SourceCalls ScopedC.NatWrapperCalls
open ScopedC.RationalUnsignedCalls
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def middle (l : PoolCalls.PoolLayout) (s : State) (cells : List (Option Value)) (top high : Nat) : State :=
  SignedCalls.siResult l s cells top high 0

def izeroResult (l : PoolCalls.PoolLayout) (s : State) (cells : List (Option Value)) (top high : Nat) : State :=
  SignedCalls.siResult l (middle l s cells top high) (cells2 l s cells top high 0)
    (top+1+1) (high2 top high) 0

def result (l : PoolCalls.PoolLayout) (s : State) (cells : List (Option Value)) (top high : Nat) : Value :=
  DyadicCasts.value (SignedValues.value s.nats.values.length 0)
    (SignedValues.value (middle l s cells top high).nats.values.length 0) true

def rawZero : Value := .integer ⟨⟨true,32⟩,0⟩

def initializer : Expr := .record [.call (.var "si") [.nat 0],.call (.var "si") [.nat 0],.nat 1]

theorem binary_env (l : PoolCalls.PoolLayout) (s : State) (cells : List (Option Value))
    (top high n : Nat) (env : Env) :
    binaryResult l {s with env:=env} cells top high n={binaryResult l s cells top high n with env:=env} := by
  unfold binaryResult PoolCalls.keepResult
  split <;> rfl

theorem si_env (l : PoolCalls.PoolLayout) (s : State) (cells : List (Option Value))
    (top high n : Nat) (env : Env) :
    SignedCalls.siResult l {s with env:=env} cells top high n=
      {SignedCalls.siResult l s cells top high n with env:=env} := by
  unfold SignedCalls.siResult
  rw [binary_env l s cells top high n env]
  exact binary_env l (binaryResult l s cells top high n)
    (cells.set top (some (.natObject s.nats.values.length))) (top+1) (max high (top+1)) 0 env

theorem si_preserves {l : PoolCalls.PoolLayout} {s : State} {cells : List (Option Value)}
    {top high n slot m : Nat} (live : NatArena.Borrow s.nats slot m) :
    NatArena.Borrow (SignedCalls.siResult l s cells top high n).nats slot m :=
  binary_result_preserves (binary_result_preserves live)

theorem pop_env {s t : State} (length : t.heap.length=s.heap.length) (environment : t.env=s.env) :
    popScope s {t with env:=[]}=t := by
  cases t
  simp_all [popScope]

/-- Four actual zero-Nat allocations/keeps from the two real si(0) calls,
followed by actual source I initialization, cast and return. -/
theorem izero_closed (code : List Function) (installed : Generated.f_izero∈code)
    (siInstalled : Generated.f_si∈code) (smakeInstalled : Generated.f_smake∈code)
    (nzInstalled : Generated.f_nz∈code) (nuInstalled : Generated.f_nu∈code)
    (neInstalled : Generated.f_ne∈code) (keepInstalled : Generated.f_keep∈code)
    {l : PoolCalls.PoolLayout} {s : State} {cells : List (Option Value)} {top high : Nat}
    (context : PoolCalls.GenericPoolContext l s cells top high) (room : top+3<PoolCalls.capacity) :
    SourceCall Header.layout code 6 "izero" [] s (result l s cells top high) (izeroResult l s cells top high) := by
  let mid := middle l s cells top high
  let final := izeroResult l s cells top high
  let before : State := {s with env:=[]}
  let afterFirst : State := {mid with env:=[]}
  let after : State := {final with env:=[]}
  let lo := SignedValues.value s.nats.values.length 0
  let hi := SignedValues.value mid.nats.values.length 0
  have room1 : top+1<PoolCalls.capacity := by omega
  have room3 : (top+1+1)+1<PoolCalls.capacity := by omega
  have c1 := si_context (n:=0) context room1
  have ctxBefore := PoolCalls.context_env context []
  have ctxMiddle := PoolCalls.context_env c1 []
  have firstProof : SourceCall Header.layout code 5 "si" [rawZero] before lo afterFirst := by
    have h := SignedCalls.si_call (n:=0) (input:=rawZero) code siInstalled smakeInstalled nzInstalled
      nuInstalled neInstalled keepInstalled ctxBefore room1 (by decide) rfl
    simpa only [before,afterFirst,lo,mid,middle,si_env] using h
  have secondProof : SourceCall Header.layout code 5 "si" [rawZero] afterFirst hi after := by
    have h := SignedCalls.si_call (n:=0) (input:=rawZero) code siInstalled smakeInstalled nzInstalled
      nuInstalled neInstalled keepInstalled ctxMiddle room3 (by decide) rfl
    simpa only [afterFirst,after,hi,final,izeroResult,mid,middle,si_env] using h
  let firstEvent : CallEvents.Event Header.layout code 5 :=
    ⟨"si",[rawZero],before,lo,afterFirst,firstProof⟩
  let secondEvent : CallEvents.Event Header.layout code 5 :=
    ⟨"si",[rawZero],afterFirst,hi,after,secondProof⟩
  let service := CallEvents.append (CallEvents.one firstEvent) (CallEvents.one secondEvent)
  have answer1 : service "si" [rawZero] before=some (lo,afterFirst) :=
    CallEvents.append_left (CallEvents.one_self firstEvent)
  have lengthStep : mid.nats.values.length=s.nats.values.length+1+1 := by
    simp only [mid,middle,SignedCalls.siResult,binary_result_nats,NatArena.allocate,
      List.length_append,List.length_singleton]
  have different : afterFirst≠before := by
    intro same
    have h := congrArg (fun t : State => t.nats.values.length) same
    change mid.nats.values.length=s.nats.values.length at h
    omega
  have none1 : CallEvents.one firstEvent "si" [rawZero] afterFirst=none := by
    simp [CallEvents.one,firstEvent,different]
  have answer2 : service "si" [rawZero] afterFirst=some (hi,after) :=
    CallEvents.append_right none1 (CallEvents.one_self secondEvent)
  have expr : evalExpr Header.layout service 1000 before initializer=
      some (.aggregate [lo,hi,.integer ⟨⟨true,32⟩,1⟩],after) :=
    DyadicIntervalNegCalls.record_three Header.layout service
      (ExpressionTemplates.call_one Header.layout service (by rfl) answer1)
      (ExpressionTemplates.call_one Header.layout service (by rfl) answer2) (by rfl)
  have loLive : NatArena.Borrow after.nats s.nats.values.length 0 :=
    si_preserves (si_borrow l s cells top high 0)
  have hiLive : NatArena.Borrow after.nats mid.nats.values.length 0 :=
    si_borrow l mid (cells2 l s cells top high 0) (top+1+1) (high2 top high) 0
  have castLo : castValue Header.layout after 99 "S" lo=some lo :=
    RecordCasts.signed after 97 "S" (by decide +kernel) loLive (by decide)
  have castHi : castValue Header.layout after 99 "S" hi=some hi :=
    RecordCasts.signed after 97 "S" (by decide +kernel) hiLive (by decide)
  have castFlag : castValue Header.layout after 99 "unsigned" (.integer ⟨⟨true,32⟩,1⟩)=
      some (unsigned32 1) := by rfl
  have fields : ([("lo","S"),("hi","S"),("ok","unsigned")].zip
      [lo,hi,.integer ⟨⟨true,32⟩,1⟩]).mapM
      (fun p => castValue Header.layout after 99 p.1.2 p.2)=some [lo,hi,unsigned32 1] := by
    change (do
      let x ← castValue Header.layout after 99 "S" lo
      let y ← castValue Header.layout after 99 "S" hi
      let z ← castValue Header.layout after 99 "unsigned" (.integer ⟨⟨true,32⟩,1⟩)
      pure [x,y,z])=some [lo,hi,unsigned32 1]
    rw [castLo,castHi,castFlag]
    rfl
  have cast : castValue Header.layout after 100 "I"
      (.aggregate [lo,hi,.integer ⟨⟨true,32⟩,1⟩])=some (result l s cells top high) :=
    TypedFrames.cast_aggregate Header.layout after 99 "I" "I"
      [("lo","S"),("hi","S"),("ok","unsigned")]
      [lo,hi,.integer ⟨⟨true,32⟩,1⟩] [lo,hi,unsigned32 1]
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) rfl fields
  have shape1 := si_shape l s cells top high 0
  have shape2 := si_shape l mid (cells2 l s cells top high 0) (top+1+1) (high2 top high) 0
  have finalShape : final.heap.length=s.heap.length ∧ final.env=s.env :=
    ⟨shape2.1.trans shape1.1,shape2.2.trans shape1.2⟩
  have length : after.heap.length=before.heap.length := finalShape.1
  have env : after.env=before.env := rfl
  have body := DeclarationReturn.body Header.layout service "I" "r" initializer expr cast (by rfl)
    (by decide) (by decide) (by decide) (by decide)
  rw [LocalScope.pop_local "I" "r" (result l s cells top high) length env] at body
  apply installed_body (f:=Generated.f_izero) (rank:=5) (service:=service) installed
    (fun _ _ _ _ _ hc => CallEvents.append_closed
      (fun _ _ _ _ _ h => CallEvents.one_closed firstEvent h)
      (fun _ _ _ _ _ h => CallEvents.one_closed secondEvent h) hc) (by rfl) body
  exact ⟨DyadicCasts.record after 97 "static I" (by decide +kernel) lo hi true castLo castHi,
    (pop_env finalShape.1 finalShape.2).symm⟩

end ScopedC.DyadicZeroCalls
