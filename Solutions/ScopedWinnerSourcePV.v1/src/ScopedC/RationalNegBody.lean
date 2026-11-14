/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedC.SignedNegBody
import ScopedC.RecordCasts
import ScopedC.DeclarationReturn
import ScopedC.LocalScope

namespace ScopedC.RationalNegCalls
open ScopedC.Syntax ScopedC.Machine ScopedC.SourceCalls
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def value (mag negative den : Nat) : Value :=
  .record "Q" [SignedNegCalls.value mag negative,.natObject den]

def frame (s : State) (mag : Nat) (b : Bool) (den : Nat) : State :=
  OneFrames.frame s "Q" "a" (value mag (SignedNegCalls.bit b) den)

theorem initialized (mag negative den : Nat) :
    Machine.initialized 1000 (value mag negative den)=true := by rfl

theorem arguments (s : State) (mag : Nat) (b : Bool) (den : Nat)
    (cast : castValue Header.layout {s with env:=[]} 100 "Q" (value mag (SignedNegCalls.bit b) den)=
      some (value mag (SignedNegCalls.bit b) den)) :
    bindArgs Header.layout Generated.f_qn.parameters [value mag (SignedNegCalls.bit b) den] s=
      some (frame s mag b den) := by
  exact TypedFrames.bind_one Header.layout s "Q" "a" _ _ cast

theorem eval_var (call : Call) (fuel : Nat) (s : State) (mag : Nat) (b : Bool) (den : Nat) :
    evalExpr Header.layout call (fuel+1) (frame s mag b den) (.var "a")=
      some (value mag (SignedNegCalls.bit b) den,frame s mag b den) := by
  exact TypedFrames.allocate_eval Header.layout call fuel {s with env:=[]}
    "Q" "a" _ (initialized _ _ _) (by decide) (by decide) (by decide) (by decide)

theorem eval_num (call : Call) (fuel : Nat) (s : State) (mag : Nat) (b : Bool) (den : Nat) :
    evalExpr Header.layout call (fuel+2) (frame s mag b den) (.field "." (.var "a") "num")=
      some (SignedNegCalls.value mag (SignedNegCalls.bit b),frame s mag b den) := by
  apply ExpressionTemplates.field Header.layout call (eval_var call fuel s mag b den)
  rfl

theorem eval_den (call : Call) (fuel : Nat) (s : State) (mag : Nat) (b : Bool) (den : Nat) :
    evalExpr Header.layout call (fuel+2) (frame s mag b den) (.field "." (.var "a") "den")=
      some (.natObject den,frame s mag b den) := by
  apply ExpressionTemplates.field Header.layout call (eval_var call fuel s mag b den)
  rfl

def initializer : Expr := .record [
  .call (.var "sn") [.field "." (.var "a") "num"],.field "." (.var "a") "den"]

theorem expression (call : Call) (s after : State) (mag : Nat) (b : Bool) (den outNeg : Nat)
    (answer : call "sn" [SignedNegCalls.value mag (SignedNegCalls.bit b)] (frame s mag b den)=
      some (SignedNegCalls.value mag outNeg,frame after mag b den)) :
    evalExpr Header.layout call 1000 (frame s mag b den) initializer=
      some (.aggregate [SignedNegCalls.value mag outNeg,.natObject den],frame after mag b den) := by
  have left : evalExpr Header.layout call 999 (frame s mag b den)
      (.call (.var "sn") [.field "." (.var "a") "num"])=
      some (SignedNegCalls.value mag outNeg,frame after mag b den) :=
    ExpressionTemplates.call_one Header.layout call (eval_num call 996 s mag b den) answer
  exact ExpressionTemplates.record_two Header.layout call left (eval_den call 997 after mag b den)

theorem body (call : Call) (s after : State) (mag : Nat) (b : Bool) (den outNeg : Nat)
    (length : after.heap.length=s.heap.length)
    (answer : call "sn" [SignedNegCalls.value mag (SignedNegCalls.bit b)] (frame s mag b den)=
      some (SignedNegCalls.value mag outNeg,frame after mag b den))
    (cast : castValue Header.layout (frame after mag b den) 100 "Q"
      (.aggregate [SignedNegCalls.value mag outNeg,.natObject den])=some (value mag outNeg den)) :
    Run Header.layout call Generated.f_qn.body (frame s mag b den)
      (.returned (frame after mag b den) (value mag outNeg den)) := by
  have h := DeclarationReturn.body Header.layout call "Q" "r" initializer
    (expression call s after mag b den outNeg answer) cast (initialized _ _ _)
    (by decide) (by decide) (by decide) (by decide)
  have hl : (frame after mag b den).heap.length=(frame s mag b den).heap.length := by
    simp [frame,OneFrames.frame,allocate,length]
  have he : (frame after mag b den).env=(frame s mag b den).env := by
    simp [frame,OneFrames.frame,allocate,length]
  rw [LocalScope.pop_local "Q" "r" _ hl he] at h
  exact h

/-- Actual local initializer, member reads, return and frame cleanup for qn.
The only intermediate source call is closed at a strictly lower rank. -/
theorem qn_call (code : List Function) (rank : Nat) (installed : Generated.f_qn∈code)
    (service : Call)
    (closed : ∀ called args before val after,
      service called args before=some (val,after) → SourceCall Header.layout code rank called args before val after)
    {s after : State} {mag den outNeg : Nat} (b : Bool)
    (length : after.heap.length=s.heap.length) (environment : after.env=s.env)
    (parameterCast : castValue Header.layout {s with env:=[]} 100 "Q" (value mag (SignedNegCalls.bit b) den)=
      some (value mag (SignedNegCalls.bit b) den))
    (aggregateCast : castValue Header.layout (frame after mag b den) 100 "Q"
      (.aggregate [SignedNegCalls.value mag outNeg,.natObject den])=some (value mag outNeg den))
    (returnCast : castValue Header.layout (frame after mag b den) 100 "static Q"
      (value mag outNeg den)=some (value mag outNeg den))
    (answer : service "sn" [SignedNegCalls.value mag (SignedNegCalls.bit b)] (frame s mag b den)=
      some (SignedNegCalls.value mag outNeg,frame after mag b den)) :
    SourceCall Header.layout code (rank+1) "qn" [value mag (SignedNegCalls.bit b) den] s
      (value mag outNeg den) after := by
  apply installed_body (f:=Generated.f_qn) (rank:=rank) installed closed
    (arguments s mag b den parameterCast) (body service s after mag b den outNeg length answer aggregateCast)
  exact ⟨returnCast,(OneFrames.pop_frame "Q" "a" _ length environment).symm⟩

theorem qn_from_lower (code : List Function) (rank : Nat) (installed : Generated.f_qn∈code)
    {s after : State} {mag den outNeg : Nat} (b : Bool)
    (length : after.heap.length=s.heap.length) (environment : after.env=s.env)
    (parameterCast : castValue Header.layout {s with env:=[]} 100 "Q" (value mag (SignedNegCalls.bit b) den)=
      some (value mag (SignedNegCalls.bit b) den))
    (aggregateCast : castValue Header.layout (frame after mag b den) 100 "Q"
      (.aggregate [SignedNegCalls.value mag outNeg,.natObject den])=some (value mag outNeg den))
    (returnCast : castValue Header.layout (frame after mag b den) 100 "static Q"
      (value mag outNeg den)=some (value mag outNeg den))
    (lower : SourceCall Header.layout code rank "sn" [SignedNegCalls.value mag (SignedNegCalls.bit b)]
      (frame s mag b den) (SignedNegCalls.value mag outNeg) (frame after mag b den)) :
    SourceCall Header.layout code (rank+1) "qn" [value mag (SignedNegCalls.bit b) den] s
      (value mag outNeg den) after := by
  let e : CallEvents.Event Header.layout code rank :=
    ⟨"sn",[SignedNegCalls.value mag (SignedNegCalls.bit b)],frame s mag b den,
      SignedNegCalls.value mag outNeg,frame after mag b den,lower⟩
  exact qn_call code rank installed (CallEvents.one e)
    (fun _ _ _ _ _ h => CallEvents.one_closed e h) b length environment parameterCast aggregateCast returnCast
    (CallEvents.one_self e)


/-- Concrete actual qn source call: its nested sn call, typed aggregate,
return cast, Nat-token liveness and local scope cleanup are all discharged. -/
theorem qn_closed (code : List Function) (installed : Generated.f_qn∈code)
    (snInstalled : Generated.f_sn∈code) (smakeInstalled : Generated.f_smake∈code)
    (nzInstalled : Generated.f_nz∈code) (nuInstalled : Generated.f_nu∈code)
    (neInstalled : Generated.f_ne∈code) (keepInstalled : Generated.f_keep∈code)
    {l : PoolCalls.PoolLayout} {s : State} {cells : List (Option Value)}
    {top high mag n den d : Nat} (b : Bool)
    (context : PoolCalls.GenericPoolContext l s cells top high) (room : top<PoolCalls.capacity)
    (magLive : NatArena.Borrow s.nats mag n) (denLive : NatArena.Borrow s.nats den d) :
    SourceCall Header.layout code 6 "qn" [value mag (SignedNegCalls.bit b) den] s
      (value mag (if n==0 then 0 else SignedNegCalls.bit (!b)) den)
      (NatWrapperCalls.binaryResult l s cells top high 0) := by
  let next := NatWrapperCalls.binaryResult l s cells top high 0
  let sign := if n==0 then 0 else SignedNegCalls.bit (!b)
  have ctxFrame : PoolCalls.GenericPoolContext l (frame s mag b den) cells top high :=
    OneFrames.context_frame context "Q" "a" (value mag (SignedNegCalls.bit b) den)
  have move : NatWrapperCalls.binaryResult l (frame s mag b den) cells top high 0=
      frame next mag b den := by
    change PoolCalls.keepResult l
      (OneFrames.frame {s with nats:=(NatArena.allocate s.nats 0).2} "Q" "a"
        (value mag (SignedNegCalls.bit b) den)) cells top high s.nats.values.length =
      OneFrames.frame (PoolCalls.keepResult l {s with nats:=(NatArena.allocate s.nats 0).2}
        cells top high s.nats.values.length) "Q" "a" (value mag (SignedNegCalls.bit b) den)
    exact OneFrames.result_frame (PoolCalls.context_nats context (NatArena.allocate s.nats 0).2)
      "Q" "a" (value mag (SignedNegCalls.bit b) den)
  have lower : SourceCall Header.layout code 5 "sn"
      [SignedNegCalls.value mag (SignedNegCalls.bit b)] (frame s mag b den)
      (SignedNegCalls.value mag sign) (frame next mag b den) := by
    have h := SignedNegCalls.sn_closed code snInstalled smakeInstalled nzInstalled nuInstalled
      neInstalled keepInstalled b ctxFrame room magLive
    simpa only [move,sign] using h
  have magAfter : NatArena.Borrow next.nats mag n := SignedNegCalls.result_borrow magLive
  have denAfter : NatArena.Borrow next.nats den d := SignedNegCalls.result_borrow denLive
  have signBound : sign<2^32 := by
    dsimp only [sign]
    split
    · decide
    · exact SignedNegCalls.bit_bound (!b)
  have shape := SignedNegCalls.result_shape l s cells top high
  exact qn_from_lower code 5 installed (s:=s) (after:=next) b shape.1 shape.2
    (RecordCasts.rational_record {s with env:=[]} 97 "Q" (by decide +kernel)
      magLive denLive (SignedNegCalls.bit_bound b))
    (RecordCasts.rational_aggregate (frame next mag b den) 97 magAfter denAfter signBound)
    (RecordCasts.rational_record (frame next mag b den) 97 "static Q" (by decide +kernel)
      magAfter denAfter signBound) lower

end ScopedC.RationalNegCalls
