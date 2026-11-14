/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedC.SignedAddBody
import ScopedC.SignedNormalization

namespace ScopedC.NumericSignedAddRefinement
open ScopedC.Syntax ScopedC.Machine ScopedC.SourceCalls
open ScopedC.DyadicRepresentation
open ScopedNumerical
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Real source sa implements the original Signed.add and returns a zero-sign
normalized value. Comparison helpers may consume that additional invariant. -/
theorem sa_math (code : List Function) (installed : Generated.f_sa∈code)
    (naInstalled : Generated.f_na∈code) (nsInstalled : Generated.f_ns∈code)
    (nleInstalled : Generated.f_nle∈code) (smakeInstalled : Generated.f_smake∈code)
    (nzInstalled : Generated.f_nz∈code) (nuInstalled : Generated.f_nu∈code)
    (neInstalled : Generated.f_ne∈code) (keepInstalled : Generated.f_keep∈code)
    {l : PoolCalls.PoolLayout} {s : State} {cells : List (Option Value)} {top high : Nat}
    (a b : Endpoint) (aLive : a.Live s) (bLive : b.Live s)
    (context : PoolCalls.GenericPoolContext l s cells top high) (room : top+1<PoolCalls.capacity) :
    SourceCall Header.layout code 5 "sa" [a.source,b.source] s (SignedAddCalls.result s a b)
        (SignedAddCalls.saResult l s cells top high a b) ∧
    NumericRepresentation.signed s a.source=some a.mathematical ∧
    NumericRepresentation.signed s b.source=some b.mathematical ∧
    NumericRepresentation.signed (SignedAddCalls.saResult l s cells top high a b)
        (SignedAddCalls.result s a b)=some (Signed.add a.mathematical b.mathematical) ∧
    (Signed.add a.mathematical b.mathematical).value=a.mathematical.value+b.mathematical.value ∧
    SignedNormalization.ZeroNormalized (Signed.add a.mathematical b.mathematical) := by
  refine ⟨SignedAddCalls.sa_closed code installed naInstalled nsInstalled nleInstalled smakeInstalled
    nzInstalled nuInstalled neInstalled keepInstalled a b aLive bLive context room,
    Endpoint.decoded aLive,Endpoint.decoded bLive,?_,Signed.value_add _ _,SignedNormalization.add_normalized _ _⟩
  have decoded := NumericSignedMultiplyRefinement.signed_made (SignedAddCalls.negative a b)
    (RationalUnsignedCalls.si_borrow l s cells top high (SignedAddCalls.magnitude a b))
  rw [SignedAddCalls.mathematical] at decoded
  exact decoded

end ScopedC.NumericSignedAddRefinement
