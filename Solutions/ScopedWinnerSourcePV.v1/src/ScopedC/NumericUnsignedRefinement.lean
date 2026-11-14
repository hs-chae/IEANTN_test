/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedC.NumericRepresentation
import ScopedC.RationalUnsignedCall

namespace ScopedC.NumericUnsignedRefinement
open ScopedC.Syntax ScopedC.Machine ScopedC.SourceCalls ScopedC.NatWrapperCalls
open ScopedNumerical
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- The actual source unsigned-to-rational constructor returns exactly the
mathematical unsigned input; its denominator is a newly allocated live one. -/
theorem qi_math (code : List Function) (installed : Generated.f_qi∈code)
    (siInstalled : Generated.f_si∈code) (smakeInstalled : Generated.f_smake∈code)
    (nzInstalled : Generated.f_nz∈code) (nuInstalled : Generated.f_nu∈code)
    (neInstalled : Generated.f_ne∈code) (keepInstalled : Generated.f_keep∈code)
    {l : PoolCalls.PoolLayout} {s : State} {cells : List (Option Value)} {top high n : Nat}
    (context : PoolCalls.GenericPoolContext l s cells top high) (room : top+2<PoolCalls.capacity)
    (bound : n<2^32) :
    SourceCall Header.layout code 6 "qi" [unsigned32 n] s
        (RecordCasts.rational s.nats.values.length 0
          (SignedCalls.siResult l s cells top high n).nats.values.length)
        (RationalUnsignedCalls.qiResult l s cells top high n) ∧
    NumericRepresentation.rational (RationalUnsignedCalls.qiResult l s cells top high n)
        (RecordCasts.rational s.nats.values.length 0
          (SignedCalls.siResult l s cells top high n).nats.values.length)=some ⟨⟨n,false⟩,1⟩ ∧
    Rational.value ⟨⟨n,false⟩,1⟩=(n:Rat) := by
  refine ⟨RationalUnsignedCalls.qi_closed code installed siInstalled smakeInstalled nzInstalled
    nuInstalled neInstalled keepInstalled context room bound,?_,?_⟩
  · exact NumericRepresentation.rational_value false
      (RationalUnsignedCalls.qi_mag_live l s cells top high n)
      (RationalUnsignedCalls.qi_den_live l s cells top high n) (by decide)
  · simp [Rational.value,Signed.value]

end ScopedC.NumericUnsignedRefinement
