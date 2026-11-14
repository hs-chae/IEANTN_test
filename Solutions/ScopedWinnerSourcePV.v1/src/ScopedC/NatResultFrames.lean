/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedC.NatResultInvariants
import ScopedC.TwoFrames

namespace ScopedC.NatWrapperCalls
open ScopedC.Machine ScopedC.PoolCalls
set_option autoImplicit false
set_option maxHeartbeats 0

theorem binary_result_one_frame {l : PoolLayout} {s : State} {cells : List (Option Value)}
    {top high result : Nat} (context : GenericPoolContext l s cells top high)
    (type name : String) (value : Value) :
    binaryResult l (OneFrames.frame s type name value) cells top high result =
      OneFrames.frame (binaryResult l s cells top high result) type name value := by
  exact OneFrames.result_frame (context_nats context (NatArena.allocate s.nats result).2) _ _ _

theorem binary_result_two_frame {l : PoolLayout} {s : State} {cells : List (Option Value)}
    {top high result : Nat} (context : GenericPoolContext l s cells top high)
    (type name : String) (value : Value) (secondType secondName : String) (secondValue : Value) :
    binaryResult l (TwoFrames.frame s type name value secondType secondName secondValue) cells top high result =
      TwoFrames.frame (binaryResult l s cells top high result) type name value secondType secondName secondValue := by
  exact TwoFrames.result_frame (context_nats context (NatArena.allocate s.nats result).2) _ _ _ _ _ _

end ScopedC.NatWrapperCalls
