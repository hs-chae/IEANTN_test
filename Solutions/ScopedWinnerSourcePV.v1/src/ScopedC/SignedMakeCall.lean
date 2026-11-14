/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedC.SignedFrames
import ScopedC.SignedValues
import ScopedC.LocalScope

namespace ScopedC.SignedCalls
open ScopedC.Syntax ScopedC.Machine ScopedC.SourceCalls ScopedC.PoolCalls ScopedC.NatWrapperCalls
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem smake_call (code : List Function) (installed : Generated.f_smake ∈ code)
    (nzInstalled : Generated.f_nz ∈ code) (nuInstalled : Generated.f_nu ∈ code)
    (neInstalled : Generated.f_ne ∈ code) (keepInstalled : Generated.f_keep ∈ code)
    {l : PoolLayout} {s : State} {cells : List (Option Value)}
    {top high mag n neg : Nat} {input : Value}
    (context : GenericPoolContext l s cells top high) (room : top < capacity)
    (live : NatArena.Borrow s.nats mag n) (negBound : neg < 2^32)
    (parameter : castValue Header.layout (allocate {s with env:=[]} "N" "mag" (some (.natObject mag)))
      100 "unsigned int" input = some (unsigned32 neg)) :
    SourceCall Header.layout code 4 "smake" [.natObject mag,input] s
      (SignedValues.value mag (if n==0 then 0 else neg)) (binaryResult l s cells top high 0) := by
  let frame := SignedFrames.frame s mag neg
  let next := binaryResult l s cells top high 0
  let after := SignedFrames.frame next mag neg
  let sign := if n==0 then 0 else neg
  let result := SignedValues.value mag sign
  have nextShape : next.heap.length = s.heap.length ∧ next.env = s.env :=
    ⟨(keep_result_shape l {s with nats:=(NatArena.allocate s.nats 0).2}
      cells top high s.nats.values.length).1,
      (keep_result_shape l {s with nats:=(NatArena.allocate s.nats 0).2}
      cells top high s.nats.values.length).2.1⟩
  have afterLive : NatArena.Borrow after.nats mag n := by
    have index : mag < s.nats.values.length := (List.getElem?_eq_some_iff.mp live.1).choose
    have hnats : after.nats = (NatArena.allocate s.nats 0).2 := by
      dsimp only [after,SignedFrames.frame,TwoFrames.frame,next,binaryResult,allocate]
      rw [keep_result_nats]
    rw [hnats]
    constructor
    · simpa only [NatArena.allocate,List.getElem?_append_left index] using live.1
    · simpa only [NatArena.allocate,if_neg (Nat.ne_of_lt index)] using live.2
  have signBound : sign < 2^32 := by
    dsimp only [sign]
    split
    · decide
    · exact negBound
  have zeroCall : SourceCall Header.layout code 3 "nz" [.natObject mag] frame
      (PrimitiveCalls.u32 (n==0)) after := by
    have h := nz_call code nzInstalled nuInstalled neInstalled keepInstalled
      (SignedFrames.context context mag neg) room live
    simpa only [SignedFrames.result_frame context] using h
  let event : CallEvents.Event Header.layout code 3 :=
    ⟨"nz",[.natObject mag],frame,PrimitiveCalls.u32 (n==0),after,zeroCall⟩
  let service := CallEvents.one event
  have test : evalExpr Header.layout service 998 frame
      (.call (.var "nz") [.var "mag"]) = some (PrimitiveCalls.u32 (n==0),after) :=
    ExpressionTemplates.call_one Header.layout service
      (SignedFrames.eval_mag service 996 s mag neg) (CallEvents.one_self event)
  have branch : evalExpr Header.layout service 998 after
      (if truth (PrimitiveCalls.u32 (n==0)) then .uint 0 else .var "neg") =
      some (unsigned32 sign,after) := by
    have truth32 (b : Bool) : truth (PrimitiveCalls.u32 b) = b := by cases b <;> rfl
    rw [truth32]
    by_cases hz : (n==0) = true
    · simp only [hz,↓reduceIte,sign]
      rfl
    · simp only [hz,↓reduceIte,Bool.false_eq_true,sign]
      exact SignedFrames.eval_neg service 997 next mag neg
  have conditional : evalExpr Header.layout service 999 frame
      (.conditional (.call (.var "nz") [.var "mag"]) (.uint 0) (.var "neg")) =
      some (unsigned32 sign,after) := ExpressionTemplates.conditional Header.layout service test branch
  have expression : evalExpr Header.layout service 1000 frame
      (.record [.var "mag",.conditional (.call (.var "nz") [.var "mag"]) (.uint 0) (.var "neg")]) =
      some (.aggregate [.natObject mag,unsigned32 sign],after) :=
    ExpressionTemplates.record_two Header.layout service
      (SignedFrames.eval_mag service 998 s mag neg) conditional
  have shape : after.heap.length = frame.heap.length ∧ after.env = frame.env := by
    constructor
    · simpa only [after,frame,SignedFrames.frame,TwoFrames.frame,allocate,List.length_append,
        List.length_singleton] using congrArg (fun x => x+2) nextShape.1
    · simp only [after,frame,SignedFrames.frame,TwoFrames.frame,allocate,List.length_append,List.length_singleton,nextShape.1]
  have statement : Run Header.layout service Generated.f_smake.body frame (.returned after result) := by
    have h := DeclarationReturn.body Header.layout service "S" "r" _ expression
      (SignedValues.cast_aggregate afterLive signBound) (SignedValues.initialized mag sign)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    rw [LocalScope.pop_local "S" "r" result shape.1 shape.2] at h
    exact h
  apply installed_body (rank:=3) (service:=service) installed
    (fun _ _ _ _ _ h => CallEvents.one_closed event h)
    (SignedFrames.bind_raw live parameter) statement
  change castValue Header.layout after 100 "static S" result = some result ∧ next = popScope s after
  constructor
  · exact SignedValues.cast_record "static S" (by decide +kernel) afterLive signBound
  · exact (TwoFrames.pop_frame _ _ _ _ _ _ nextShape.1 nextShape.2).symm

end ScopedC.SignedCalls
