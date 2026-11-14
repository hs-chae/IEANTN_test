/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedC.SignedMultiplyBody

namespace ScopedC.NumericSignedMultiplyRefinement
open ScopedC.Syntax ScopedC.Machine ScopedC.SourceCalls
open ScopedC.DyadicRepresentation
open ScopedNumerical
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem signed_made {s : State} {slot n : Nat} (b : Bool)
    (live : NatArena.Borrow s.nats slot n) :
    NumericRepresentation.signed s (SignedValues.value slot (if n==0 then 0 else SignedNegCalls.bit b))=
      some (Signed.make n b) := by
  by_cases zero : n=0
  · simpa [Signed.make,SignedNegCalls.bit,zero] using NumericRepresentation.signed_value false live
  · simpa [Signed.make,zero] using NumericRepresentation.signed_value b live

/-- The real source signed-product body implements the existing Signed.mul,
including zero-sign normalization and its exact integer product value. -/
theorem sm_math (code : List Function) (installed : Generated.f_sm∈code)
    (nmInstalled : Generated.f_nm∈code) (smakeInstalled : Generated.f_smake∈code)
    (nzInstalled : Generated.f_nz∈code) (nuInstalled : Generated.f_nu∈code)
    (neInstalled : Generated.f_ne∈code) (keepInstalled : Generated.f_keep∈code)
    {l : PoolCalls.PoolLayout} {s : State} {cells : List (Option Value)} {top high : Nat}
    (a b : Endpoint) (aLive : a.Live s) (bLive : b.Live s)
    (context : PoolCalls.GenericPoolContext l s cells top high) (room : top+1<PoolCalls.capacity) :
    SourceCall Header.layout code 5 "sm" [a.source,b.source] s (SignedMultiplyCalls.result s a b)
        (SignedMultiplyCalls.smResult l s cells top high a b) ∧
    NumericRepresentation.signed s a.source=some a.mathematical ∧
    NumericRepresentation.signed s b.source=some b.mathematical ∧
    NumericRepresentation.signed (SignedMultiplyCalls.smResult l s cells top high a b)
        (SignedMultiplyCalls.result s a b)=some (Signed.mul a.mathematical b.mathematical) ∧
    (Signed.mul a.mathematical b.mathematical).value=a.mathematical.value*b.mathematical.value := by
  refine ⟨SignedMultiplyCalls.sm_closed code installed nmInstalled smakeInstalled nzInstalled nuInstalled
    neInstalled keepInstalled a b aLive bLive context room,Endpoint.decoded aLive,Endpoint.decoded bLive,?_,
    Signed.value_mul _ _⟩
  exact signed_made (a.negative != b.negative)
    (RationalUnsignedCalls.si_borrow l s cells top high (a.magnitude*b.magnitude))

end ScopedC.NumericSignedMultiplyRefinement
