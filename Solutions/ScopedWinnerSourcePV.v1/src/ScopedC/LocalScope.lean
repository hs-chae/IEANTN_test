/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedC.SourceCalls

namespace ScopedC.LocalScope
open ScopedC.Machine
set_option autoImplicit false
set_option maxHeartbeats 0

theorem pop_local {s t : State} (type name : String) (v : Value)
    (length : t.heap.length = s.heap.length) (environment : t.env = s.env) :
    popScope s (allocate t type name (some v)) = t := by
  cases t
  simp_all [popScope,allocate]

end ScopedC.LocalScope
