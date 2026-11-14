/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedC.NatZeroCall

namespace ScopedC.NatWrapperCalls
open ScopedC.Syntax ScopedC.Machine ScopedC.PoolCalls
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem binary_result_nats (l : PoolLayout) (s : State) (cells : List (Option Value))
    (top high result : Nat) :
    (binaryResult l s cells top high result).nats = (NatArena.allocate s.nats result).2 := by
  exact keep_result_nats l _ cells top high s.nats.values.length

theorem binary_result_context {l : PoolLayout} {s : State} {cells : List (Option Value)}
    {top high result : Nat} (context : GenericPoolContext l s cells top high) (room : top < capacity) :
    GenericPoolContext l (binaryResult l s cells top high result)
      (cells.set top (some (.natObject s.nats.values.length))) (top+1) (max high (top+1)) :=
  keep_result_context (context_nats context (NatArena.allocate s.nats result).2) room

theorem binary_result_borrow (l : PoolLayout) (s : State) (cells : List (Option Value))
    (top high result : Nat) :
    NatArena.Borrow (binaryResult l s cells top high result).nats s.nats.values.length result := by
  rw [binary_result_nats]
  exact NatArena.allocate_borrow s.nats result

theorem binary_result_preserves {l : PoolLayout} {s : State} {cells : List (Option Value)}
    {top high result slot n : Nat} (live : NatArena.Borrow s.nats slot n) :
    NatArena.Borrow (binaryResult l s cells top high result).nats slot n := by
  have index : slot < s.nats.values.length := (List.getElem?_eq_some_iff.mp live.1).choose
  rw [binary_result_nats]
  constructor
  · simpa only [NatArena.allocate,List.getElem?_append_left index] using live.1
  · simpa only [NatArena.allocate,if_neg (Nat.ne_of_lt index)] using live.2

end ScopedC.NatWrapperCalls
