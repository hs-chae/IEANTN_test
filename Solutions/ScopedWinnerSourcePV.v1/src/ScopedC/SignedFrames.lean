/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedC.NatZeroCall
import ScopedC.TwoFrames
import ScopedC.DeclarationReturn

namespace ScopedC.SignedFrames
open ScopedC.Syntax ScopedC.Machine ScopedC.SourceCalls ScopedC.PoolCalls ScopedC.NatWrapperCalls
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def frame (s : State) (slot neg : Nat) : State :=
  TwoFrames.frame s "N" "mag" (.natObject slot) "unsigned int" "neg" (unsigned32 neg)

theorem bind_raw {s : State} {slot n neg : Nat} {input : Value}
    (live : NatArena.Borrow s.nats slot n)
    (parameter : castValue Header.layout (allocate {s with env:=[]} "N" "mag" (some (.natObject slot)))
      100 "unsigned int" input = some (unsigned32 neg)) :
    bindArgs Header.layout Generated.f_smake.parameters [.natObject slot,input] s =
      some (frame s slot neg) := by
  exact TypedFrames.bind_two Header.layout s "N" "mag" "unsigned int" "neg"
    (.natObject slot) input (.natObject slot) (unsigned32 neg)
    (PrimitiveCalls.cast_N live) parameter

theorem bind {s : State} {slot n neg : Nat} (live : NatArena.Borrow s.nats slot n)
    (bound : neg < 2^32) :
    bindArgs Header.layout Generated.f_smake.parameters [.natObject slot,unsigned32 neg] s =
      some (frame s slot neg) := by
  exact TypedFrames.bind_two Header.layout s "N" "mag" "unsigned int" "neg"
    (.natObject slot) (unsigned32 neg) (.natObject slot) (unsigned32 neg)
    (PrimitiveCalls.cast_N live)
    (cast_unsigned (allocate {s with env:=[]} "N" "mag" (some (.natObject slot))) neg bound)

theorem eval_mag (call : Call) (fuel : Nat) (s : State) (slot neg : Nat) :
    evalExpr Header.layout call (fuel+1) (frame s slot neg) (.var "mag") =
      some (.natObject slot,frame s slot neg) := by
  rw [evalExpr]
  simp [getVar,frame,TwoFrames.frame,allocate,List.lookup,Machine.read,nested,initialized,
    List.getElem?_append]

theorem eval_neg (call : Call) (fuel : Nat) (s : State) (slot neg : Nat) :
    evalExpr Header.layout call (fuel+1) (frame s slot neg) (.var "neg") =
      some (unsigned32 neg,frame s slot neg) := by
  exact TypedFrames.allocate_eval Header.layout call fuel
    (allocate {s with env:=[]} "N" "mag" (some (.natObject slot)))
    "unsigned int" "neg" (unsigned32 neg) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem context {l : PoolLayout} {s : State} {cells : List (Option Value)} {top high : Nat}
    (h : GenericPoolContext l s cells top high) (slot neg : Nat) :
    GenericPoolContext l (frame s slot neg) cells top high := TwoFrames.context_frame h _ _ _ _ _ _

theorem result_frame {l : PoolLayout} {s : State} {cells : List (Option Value)} {top high slot neg : Nat}
    (h : GenericPoolContext l s cells top high) :
    binaryResult l (frame s slot neg) cells top high 0 =
      frame (binaryResult l s cells top high 0) slot neg := by
  exact TwoFrames.result_frame (context_nats h (NatArena.allocate s.nats 0).2) _ _ _ _ _ _

end ScopedC.SignedFrames
