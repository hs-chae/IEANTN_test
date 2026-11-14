/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedC.DyadicZeroBody
import ScopedC.DyadicValueEquivalence
import LeanCert.Engine.FinSumDyadic

namespace ScopedC.NumericDyadicZeroRefinement
open ScopedC.Syntax ScopedC.Machine ScopedC.SourceCalls
open ScopedC.DyadicRepresentation ScopedC.DyadicValueEquivalence
open LeanCert.Core LeanCert.Engine
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem zero_decoded {l : PoolCalls.PoolLayout} {s : State} {cells : List (Option Value)} {top high : Nat} :
    interval (DyadicZeroCalls.izeroResult l s cells top high) (DyadicZeroCalls.result l s cells top high)=
      some (words100 0 0 (by decide),true) := by
  let lo : Endpoint := ⟨s.nats.values.length,0,false⟩
  let hi : Endpoint := ⟨(DyadicZeroCalls.middle l s cells top high).nats.values.length,0,false⟩
  have loLive : lo.Live (DyadicZeroCalls.izeroResult l s cells top high) :=
    DyadicZeroCalls.si_preserves (RationalUnsignedCalls.si_borrow l s cells top high 0)
  have hiLive : hi.Live (DyadicZeroCalls.izeroResult l s cells top high) :=
    RationalUnsignedCalls.si_borrow l (DyadicZeroCalls.middle l s cells top high)
      (RationalUnsignedCalls.cells2 l s cells top high 0) (top+1+1) (RationalUnsignedCalls.high2 top high) 0
  exact decoded_interval lo hi true loLive hiLive (by change (0:Int)≤0; exact le_rfl)

theorem old_zero_values : SameValues (words100 0 0 (by decide)) finSumZero := by
  apply zero_same
  · norm_num [finSumZero,IntervalDyadic.singleton,LeanCert.Core.Dyadic.zero,
      LeanCert.Core.Dyadic.toRat,LeanCert.Core.Dyadic.pow2Nat]
  · norm_num [finSumZero,IntervalDyadic.singleton,LeanCert.Core.Dyadic.zero,
      LeanCert.Core.Dyadic.toRat,LeanCert.Core.Dyadic.pow2Nat]

/-- Real source initialization constructs its own zero Nat tokens. It has no
initial mathematical-output representation premise, and represents exactly the
old accumulator zero by endpoint values despite its canonical source exponent. -/
theorem izero_math (code : List Function) (installed : Generated.f_izero∈code)
    (siInstalled : Generated.f_si∈code) (smakeInstalled : Generated.f_smake∈code)
    (nzInstalled : Generated.f_nz∈code) (nuInstalled : Generated.f_nu∈code)
    (neInstalled : Generated.f_ne∈code) (keepInstalled : Generated.f_keep∈code)
    {l : PoolCalls.PoolLayout} {s : State} {cells : List (Option Value)} {top high : Nat}
    (context : PoolCalls.GenericPoolContext l s cells top high) (room : top+3<PoolCalls.capacity) :
    SourceCall Header.layout code 6 "izero" [] s (DyadicZeroCalls.result l s cells top high)
        (DyadicZeroCalls.izeroResult l s cells top high) ∧
    interval (DyadicZeroCalls.izeroResult l s cells top high) (DyadicZeroCalls.result l s cells top high)=
      some (words100 0 0 (by decide),true) ∧
    Represents (DyadicZeroCalls.izeroResult l s cells top high) (DyadicZeroCalls.result l s cells top high)
      finSumZero true := by
  exact ⟨DyadicZeroCalls.izero_closed code installed siInstalled smakeInstalled nzInstalled nuInstalled
    neInstalled keepInstalled context room,zero_decoded,_,zero_decoded,old_zero_values⟩

end ScopedC.NumericDyadicZeroRefinement
