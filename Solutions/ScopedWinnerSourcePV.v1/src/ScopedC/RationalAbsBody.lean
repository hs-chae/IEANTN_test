/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedC.RationalNegBody

namespace ScopedC.RationalAbsCalls
open ScopedC.Syntax ScopedC.Machine ScopedC.SourceCalls ScopedC.NatWrapperCalls
open ScopedC.RationalNegCalls (value frame)
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def zero : Value := .integer ⟨⟨true,32⟩,0⟩
def initializer : Expr := .record [
  .call (.var "smake") [.field "." (.field "." (.var "a") "num") "mag",.nat 0],
  .field "." (.var "a") "den"]

theorem expression (call : Call) (s after : State) (mag : Nat) (b : Bool) (den : Nat)
    (answer : call "smake" [.natObject mag,zero] (frame s mag b den)=
      some (SignedNegCalls.value mag 0,frame after mag b den)) :
    evalExpr Header.layout call 1000 (frame s mag b den) initializer=
      some (.aggregate [SignedNegCalls.value mag 0,.natObject den],frame after mag b den) := by
  have field : evalExpr Header.layout call 998 (frame s mag b den)
      (.field "." (.field "." (.var "a") "num") "mag")=
      some (.natObject mag,frame s mag b den) := by
    apply ExpressionTemplates.field Header.layout call
      (RationalNegCalls.eval_num call 995 s mag b den)
    rfl
  have left : evalExpr Header.layout call 999 (frame s mag b den)
      (.call (.var "smake") [.field "." (.field "." (.var "a") "num") "mag",.nat 0])=
      some (SignedNegCalls.value mag 0,frame after mag b den) :=
    ExpressionTemplates.call_two Header.layout call field (by rfl) answer
  exact ExpressionTemplates.record_two Header.layout call left
    (RationalNegCalls.eval_den call 997 after mag b den)

theorem body (call : Call) (s after : State) (mag : Nat) (b : Bool) (den : Nat)
    (length : after.heap.length=s.heap.length)
    (answer : call "smake" [.natObject mag,zero] (frame s mag b den)=
      some (SignedNegCalls.value mag 0,frame after mag b den))
    (cast : castValue Header.layout (frame after mag b den) 100 "Q"
      (.aggregate [SignedNegCalls.value mag 0,.natObject den])=some (value mag 0 den)) :
    Run Header.layout call Generated.f_qabs.body (frame s mag b den)
      (.returned (frame after mag b den) (value mag 0 den)) := by
  have h := DeclarationReturn.body Header.layout call "Q" "r" initializer
    (expression call s after mag b den answer) cast (RationalNegCalls.initialized _ _ _)
    (by decide) (by decide) (by decide) (by decide)
  have hl : (frame after mag b den).heap.length=(frame s mag b den).heap.length := by
    simp [frame,OneFrames.frame,allocate,length]
  have he : (frame after mag b den).env=(frame s mag b den).env := by
    simp [frame,OneFrames.frame,allocate,length]
  rw [LocalScope.pop_local "Q" "r" _ hl he] at h
  exact h

/-- Source qabs executes its actual smake call and copies the existing denominator.
All application casts and scope effects follow from the represented input. -/
theorem qabs_closed (code : List Function) (installed : Generated.f_qabs∈code)
    (smakeInstalled : Generated.f_smake∈code) (nzInstalled : Generated.f_nz∈code)
    (nuInstalled : Generated.f_nu∈code) (neInstalled : Generated.f_ne∈code)
    (keepInstalled : Generated.f_keep∈code)
    {l : PoolCalls.PoolLayout} {s : State} {cells : List (Option Value)}
    {top high mag n den d : Nat} (b : Bool)
    (context : PoolCalls.GenericPoolContext l s cells top high) (room : top<PoolCalls.capacity)
    (magLive : NatArena.Borrow s.nats mag n) (denLive : NatArena.Borrow s.nats den d) :
    SourceCall Header.layout code 5 "qabs" [value mag (SignedNegCalls.bit b) den] s
      (value mag 0 den) (binaryResult l s cells top high 0) := by
  let next := binaryResult l s cells top high 0
  have ctxFrame : PoolCalls.GenericPoolContext l (frame s mag b den) cells top high :=
    OneFrames.context_frame context "Q" "a" (value mag (SignedNegCalls.bit b) den)
  have move : binaryResult l (frame s mag b den) cells top high 0=frame next mag b den := by
    change PoolCalls.keepResult l
      (OneFrames.frame {s with nats:=(NatArena.allocate s.nats 0).2} "Q" "a"
        (value mag (SignedNegCalls.bit b) den)) cells top high s.nats.values.length =
      OneFrames.frame (PoolCalls.keepResult l {s with nats:=(NatArena.allocate s.nats 0).2}
        cells top high s.nats.values.length) "Q" "a" (value mag (SignedNegCalls.bit b) den)
    exact OneFrames.result_frame (PoolCalls.context_nats context (NatArena.allocate s.nats 0).2)
      "Q" "a" (value mag (SignedNegCalls.bit b) den)
  have lower : SourceCall Header.layout code 4 "smake" [.natObject mag,zero]
      (frame s mag b den) (SignedNegCalls.value mag 0) (frame next mag b den) := by
    have h := SignedCalls.smake_call code smakeInstalled nzInstalled nuInstalled neInstalled keepInstalled
      ctxFrame room magLive (show 0<2^32 by decide +kernel)
      (show castValue Header.layout
        (allocate {frame s mag b den with env:=[]} "N" "mag" (some (.natObject mag)))
        100 "unsigned int" zero=some (unsigned32 0) by rfl)
    simpa only [move,ite_self,SignedValues.value,SignedNegCalls.value] using h
  let event : CallEvents.Event Header.layout code 4 :=
    ⟨"smake",[.natObject mag,zero],frame s mag b den,SignedNegCalls.value mag 0,
      frame next mag b den,lower⟩
  let service := CallEvents.one event
  have magAfter : NatArena.Borrow next.nats mag n := SignedNegCalls.result_borrow magLive
  have denAfter : NatArena.Borrow next.nats den d := SignedNegCalls.result_borrow denLive
  have shape := SignedNegCalls.result_shape l s cells top high
  apply installed_body (f:=Generated.f_qabs) (rank:=4) installed
    (fun _ _ _ _ _ h => CallEvents.one_closed event h)
    (RationalNegCalls.arguments s mag b den
      (RecordCasts.rational_record {s with env:=[]} 97 "Q" (by decide +kernel)
        magLive denLive (SignedNegCalls.bit_bound b)))
    (body service s next mag b den shape.1 (CallEvents.one_self event)
      (RecordCasts.rational_aggregate (frame next mag b den) 97 magAfter denAfter (by decide +kernel)))
  exact ⟨RecordCasts.rational_record (frame next mag b den) 97 "static Q" (by decide +kernel)
    magAfter denAfter (by decide +kernel),
    (OneFrames.pop_frame "Q" "a" _ shape.1 shape.2).symm⟩

end ScopedC.RationalAbsCalls
