/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedC.NatUnsignedCall
import ScopedC.SignedMakeCall
import ScopedC.CallEvents
import ScopedC.OneFrames
import ScopedC.ExpressionBinary
import ScopedC.SourceCallRanks

namespace ScopedC.SignedNegCalls
open ScopedC.Syntax ScopedC.Machine ScopedC.SourceCalls ScopedC.NatWrapperCalls
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def bit (b : Bool) : Nat := if b then 1 else 0

def value (slot neg : Nat) : Value := .record "S" [.natObject slot,unsigned32 neg]

theorem initialized (slot neg : Nat) : Machine.initialized 1000 (value slot neg)=true := by rfl

def frame (s : State) (mag : Nat) (negative : Bool) : State :=
  OneFrames.frame s "S" "a" (value mag (bit negative))

theorem bit_bound (b : Bool) : bit b < 2^32 := by cases b <;> decide +kernel

theorem arguments (s : State) (mag : Nat) (b : Bool)
    (cast : castValue Header.layout {s with env:=[]} 100 "S" (value mag (bit b))=some (value mag (bit b))) :
    bindArgs Header.layout Generated.f_sn.parameters [value mag (bit b)] s =
      some (frame s mag b) := by
  exact TypedFrames.bind_one Header.layout s "S" "a" _ _ cast

theorem eval_var (call : Call) (fuel : Nat) (s : State) (mag : Nat) (b : Bool) :
    evalExpr Header.layout call (fuel+1) (frame s mag b) (.var "a") =
      some (value mag (bit b),frame s mag b) := by
  exact TypedFrames.allocate_eval Header.layout call fuel {s with env:=[]}
    "S" "a" _ (initialized _ _) (by decide) (by decide) (by decide) (by decide)

theorem eval_mag (call : Call) (fuel : Nat) (s : State) (mag : Nat) (b : Bool) :
    evalExpr Header.layout call (fuel+2) (frame s mag b) (.field "." (.var "a") "mag") =
      some (.natObject mag,frame s mag b) := by
  apply ExpressionTemplates.field Header.layout call (eval_var call fuel s mag b)
  rfl

theorem eval_neg (call : Call) (fuel : Nat) (s : State) (mag : Nat) (b : Bool) :
    evalExpr Header.layout call (fuel+2) (frame s mag b) (.field "." (.var "a") "neg") =
      some (unsigned32 (bit b),frame s mag b) := by
  apply ExpressionTemplates.field Header.layout call (eval_var call fuel s mag b)
  rfl

theorem subtract_flag (s : State) (b : Bool) :
    binaryValue Header.layout s "-" (.integer ⟨⟨true,32⟩,1⟩) (unsigned32 (bit b)) =
      some (unsigned32 (bit (!b))) := by
  cases b <;> rfl

theorem expression (call : Call) (s : State) (mag : Nat) (b : Bool)
    (out : Value) (after : State)
    (answer : call "smake" [.natObject mag,unsigned32 (bit (!b))] (frame s mag b) = some (out,after)) :
    evalExpr Header.layout call 5 (frame s mag b)
      (.call (.var "smake") [.field "." (.var "a") "mag",
        .binary "-" (.nat 1) (.field "." (.var "a") "neg")]) = some (out,after) := by
  have rhs : evalExpr Header.layout call 4 (frame s mag b)
      (.binary "-" (.nat 1) (.field "." (.var "a") "neg")) =
      some (unsigned32 (bit (!b)),frame s mag b) := by
    apply ExpressionTemplates.binary Header.layout call (by decide) (by decide) (by decide) (by decide)
      (show evalExpr Header.layout call 3 (frame s mag b) (.nat 1) =
        some (.integer ⟨⟨true,32⟩,1⟩,frame s mag b) by rfl)
      (eval_neg call 1 s mag b) (subtract_flag (frame s mag b) b)
  exact ExpressionTemplates.call_two Header.layout call (eval_mag call 2 s mag b) rhs answer

theorem body (call : Call) (s : State) (mag : Nat) (b : Bool) (out : Value) (after : State)
    (answer : call "smake" [.natObject mag,unsigned32 (bit (!b))] (frame s mag b) = some (out,after)) :
    Run Header.layout call Generated.f_sn.body (frame s mag b)
      (.returned (popScope (frame s mag b) after) out) := by
  apply Loops.StmtRun.sequence (Loops.SeqRun.returned
    (Loops.StmtRun.returnValue ⟨5,expression call s mag b out after answer⟩))
  exact ⟨rfl,rfl⟩

theorem pop_twice (s after : State) (mag : Nat) (b : Bool) :
    popScope s (popScope (frame s mag b) after) = popScope s after := by
  cases after
  simp [popScope,frame,OneFrames.frame,allocate,List.take_take]

/-- Actual sn body. Every intermediate returned call must already have a
strictly lower installed-source execution tree; no application output oracle. -/
theorem sn_call (code : List Function) (rank : Nat) (installed : Generated.f_sn∈code)
    (service : Call)
    (closed : ∀ called args before val after,
      service called args before=some (val,after) → SourceCall Header.layout code rank called args before val after)
    {s after : State} {mag outNeg : Nat} (b : Bool)
    (parameterCast : castValue Header.layout {s with env:=[]} 100 "S" (value mag (bit b))=
      some (value mag (bit b)))
    (returnCast : castValue Header.layout (popScope (frame s mag b) after) 100 "static S"
      (value mag outNeg)=some (value mag outNeg))
    (answer : service "smake" [.natObject mag,unsigned32 (bit (!b))] (frame s mag b) =
      some (value mag outNeg,after)) :
    SourceCall Header.layout code (rank+1) "sn" [value mag (bit b)] s
      (value mag outNeg) (popScope s after) := by
  apply installed_body (f:=Generated.f_sn) (rank:=rank) installed closed
    (arguments s mag b parameterCast) (body service s mag b _ after answer)
  exact ⟨returnCast,(pop_twice s after mag b).symm⟩

/-- Instantiation from a genuine lower-rank smake execution. The finite service
is constructed here, and its every answer is justified by that execution. -/
theorem sn_from_lower (code : List Function) (rank : Nat) (installed : Generated.f_sn∈code)
    {s after : State} {mag outNeg : Nat} (b : Bool)
    (parameterCast : castValue Header.layout {s with env:=[]} 100 "S" (value mag (bit b))=
      some (value mag (bit b)))
    (returnCast : castValue Header.layout (popScope (frame s mag b) after) 100 "static S"
      (value mag outNeg)=some (value mag outNeg))
    (lower : SourceCall Header.layout code rank "smake" [.natObject mag,unsigned32 (bit (!b))]
      (frame s mag b) (value mag outNeg) after) :
    SourceCall Header.layout code (rank+1) "sn" [value mag (bit b)] s
      (value mag outNeg) (popScope s after) := by
  let e : CallEvents.Event Header.layout code rank :=
    ⟨"smake",[.natObject mag,unsigned32 (bit (!b))],frame s mag b,value mag outNeg,after,lower⟩
  exact sn_call code rank installed (CallEvents.one e)
    (fun _ _ _ _ _ h => CallEvents.one_closed e h) b parameterCast returnCast (CallEvents.one_self e)


theorem result_shape (l : PoolCalls.PoolLayout) (s : State) (cells : List (Option Value))
    (top high : Nat) :
    (binaryResult l s cells top high 0).heap.length=s.heap.length ∧
    (binaryResult l s cells top high 0).env=s.env := by
  exact ⟨(PoolCalls.keep_result_shape l {s with nats:=(NatArena.allocate s.nats 0).2}
    cells top high s.nats.values.length).1,
    (PoolCalls.keep_result_shape l {s with nats:=(NatArena.allocate s.nats 0).2}
    cells top high s.nats.values.length).2.1⟩

theorem result_borrow {l : PoolCalls.PoolLayout} {s : State} {cells : List (Option Value)}
    {top high slot n : Nat} (live : NatArena.Borrow s.nats slot n) :
    NatArena.Borrow (binaryResult l s cells top high 0).nats slot n := by
  have index : slot<s.nats.values.length := (List.getElem?_eq_some_iff.mp live.1).choose
  have hnats : (binaryResult l s cells top high 0).nats=(NatArena.allocate s.nats 0).2 := by
    unfold binaryResult
    rw [PoolCalls.keep_result_nats]
  rw [hnats]
  constructor
  · simpa only [NatArena.allocate,List.getElem?_append_left index] using live.1
  · simpa only [NatArena.allocate,if_neg (Nat.ne_of_lt index)] using live.2

/-- Concrete source closure from the already closed actual smake/nz/nu/ne/keep
bodies. Both input and return casts are proved, not premises of this interface. -/
theorem sn_closed (code : List Function) (installed : Generated.f_sn∈code)
    (smakeInstalled : Generated.f_smake∈code) (nzInstalled : Generated.f_nz∈code)
    (nuInstalled : Generated.f_nu∈code) (neInstalled : Generated.f_ne∈code)
    (keepInstalled : Generated.f_keep∈code)
    {l : PoolCalls.PoolLayout} {s : State} {cells : List (Option Value)}
    {top high mag n : Nat} (b : Bool)
    (context : PoolCalls.GenericPoolContext l s cells top high) (room : top<PoolCalls.capacity)
    (live : NatArena.Borrow s.nats mag n) :
    SourceCall Header.layout code 5 "sn" [value mag (bit b)] s
      (value mag (if n==0 then 0 else bit (!b))) (binaryResult l s cells top high 0) := by
  let next := binaryResult l s cells top high 0
  let after := frame next mag b
  let sign := if n==0 then 0 else bit (!b)
  have ctxFrame : PoolCalls.GenericPoolContext l (frame s mag b) cells top high :=
    OneFrames.context_frame context "S" "a" (value mag (bit b))
  have move : binaryResult l (frame s mag b) cells top high 0=after := by
    change PoolCalls.keepResult l
      (OneFrames.frame {s with nats:=(NatArena.allocate s.nats 0).2} "S" "a" (value mag (bit b)))
      cells top high s.nats.values.length =
      OneFrames.frame (PoolCalls.keepResult l {s with nats:=(NatArena.allocate s.nats 0).2}
        cells top high s.nats.values.length) "S" "a" (value mag (bit b))
    exact OneFrames.result_frame (PoolCalls.context_nats context (NatArena.allocate s.nats 0).2)
      "S" "a" (value mag (bit b))
  have lower : SourceCall Header.layout code 4 "smake" [.natObject mag,unsigned32 (bit (!b))]
      (frame s mag b) (value mag sign) after := by
    have h := SignedCalls.smake_call code smakeInstalled nzInstalled nuInstalled neInstalled keepInstalled
      ctxFrame room live (bit_bound (!b))
      (show castValue Header.layout
        (allocate {frame s mag b with env:=[]} "N" "mag" (some (.natObject mag)))
        100 "unsigned int" (unsigned32 (bit (!b)))=some (unsigned32 (bit (!b))) by
          change ((Scalar.cast ⟨false,32⟩ ⟨⟨false,32⟩,(bit (!b):Int)⟩) >>=
            fun x => some (Value.integer x))=some (unsigned32 (bit (!b)))
          cases b <;> rfl)
    simpa only [move,sign,value,SignedValues.value] using h
  have outLive : NatArena.Borrow after.nats mag n := result_borrow live
  have signBound : sign<2^32 := by
    dsimp only [sign]
    split
    · decide
    · exact bit_bound (!b)
  have h := sn_from_lower code 4 installed (s:=s) (after:=after) b
    (SignedValues.cast_record "S" (by decide +kernel) live (bit_bound b))
    (SignedValues.cast_record "static S" (by decide +kernel) outLive signBound) lower
  have shape := result_shape l s cells top high
  have pop : popScope s after=next := OneFrames.pop_frame "S" "a" (value mag (bit b)) shape.1 shape.2
  simpa only [pop,next,sign] using h

end ScopedC.SignedNegCalls
