/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedC.DyadicIntervalNegBody

namespace ScopedC.NumericDyadicNegRefinement
open ScopedC.Syntax ScopedC.Machine ScopedC.SourceCalls
open ScopedC.DyadicRepresentation
open LeanCert.Core
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Exact original dyadic interval-negation step, including its unchanged domain
flag, backed by actual source body calls and represented Nat-runtime storage.
The input is the source's canonical -100 representation; no arbitrary coarser
old Dyadic structure is asserted byte/field equal to that representation. -/
theorem ineg_math (code : List Function) (installed : Generated.f_ineg∈code)
    (snInstalled : Generated.f_sn∈code) (smakeInstalled : Generated.f_smake∈code)
    (nzInstalled : Generated.f_nz∈code) (nuInstalled : Generated.f_nu∈code)
    (neInstalled : Generated.f_ne∈code) (keepInstalled : Generated.f_keep∈code)
    {l : PoolCalls.PoolLayout} {s : State} {cells : List (Option Value)} {top high : Nat}
    (lo hi : Endpoint) (ok : Bool) (loLive : lo.Live s) (hiLive : hi.Live s)
    (ordered : lo.mathematical.value≤hi.mathematical.value)
    (context : PoolCalls.GenericPoolContext l s cells top high) (room : top+1<PoolCalls.capacity) :
    SourceCall Header.layout code 6 "ineg" [DyadicIntervalNegCalls.value lo hi ok] s
        (DyadicIntervalNegCalls.result lo hi ok) (DyadicIntervalNegCalls.inegResult l s cells top high) ∧
    interval s (DyadicIntervalNegCalls.value lo hi ok)=
      some (words100 lo.mathematical.value hi.mathematical.value ordered,ok) ∧
    interval (DyadicIntervalNegCalls.inegResult l s cells top high) (DyadicIntervalNegCalls.result lo hi ok)=
      some (IntervalDyadic.neg (words100 lo.mathematical.value hi.mathematical.value ordered),ok) := by
  refine ⟨DyadicIntervalNegCalls.ineg_closed code installed snInstalled smakeInstalled nzInstalled
    nuInstalled neInstalled keepInstalled lo hi ok loLive hiLive context room,
    decoded_interval lo hi ok loLive hiLive ordered,?_⟩
  have loAfter : lo.Live (DyadicIntervalNegCalls.inegResult l s cells top high) :=
    Endpoint.live_after (Endpoint.live_after loLive)
  have hiAfter : hi.Live (DyadicIntervalNegCalls.inegResult l s cells top high) :=
    Endpoint.live_after (Endpoint.live_after hiLive)
  exact decoded_negative_interval lo hi ok loAfter hiAfter ordered

end ScopedC.NumericDyadicNegRefinement
