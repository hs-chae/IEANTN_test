/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedC.NumericRepresentation

namespace ScopedC.NumericNegationRefinement
open ScopedC.Syntax ScopedC.Machine ScopedC.SourceCalls ScopedC.NatWrapperCalls
open ScopedNumerical
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Both the real source-body execution and its mathematical negation result.
The represented-input premises state storage/flag validity, not an output. -/
theorem sn_math (code : List Function) (installed : Generated.f_sn∈code)
    (smakeInstalled : Generated.f_smake∈code) (nzInstalled : Generated.f_nz∈code)
    (nuInstalled : Generated.f_nu∈code) (neInstalled : Generated.f_ne∈code)
    (keepInstalled : Generated.f_keep∈code)
    {l : PoolCalls.PoolLayout} {s : State} {cells : List (Option Value)}
    {top high mag n : Nat} (b : Bool)
    (context : PoolCalls.GenericPoolContext l s cells top high) (room : top<PoolCalls.capacity)
    (live : NatArena.Borrow s.nats mag n) :
    SourceCall Header.layout code 5 "sn" [SignedNegCalls.value mag (SignedNegCalls.bit b)] s
        (SignedNegCalls.value mag (if n==0 then 0 else SignedNegCalls.bit (!b)))
        (binaryResult l s cells top high 0) ∧
    NumericRepresentation.signed s (SignedNegCalls.value mag (SignedNegCalls.bit b))=some ⟨n,b⟩ ∧
    NumericRepresentation.signed (binaryResult l s cells top high 0)
        (SignedNegCalls.value mag (if n==0 then 0 else SignedNegCalls.bit (!b)))=
      some (Signed.negated ⟨n,b⟩) ∧
    (Signed.negated ⟨n,b⟩).value=-(Signed.value ⟨n,b⟩) := by
  exact ⟨SignedNegCalls.sn_closed code installed smakeInstalled nzInstalled nuInstalled neInstalled
    keepInstalled b context room live,NumericRepresentation.signed_value b live,
    NumericRepresentation.signed_negated b (SignedNegCalls.result_borrow live),Signed.value_negated _⟩

theorem rational_negation (a : Signed) (d : Nat) :
    Rational.value ⟨a.negated,d⟩=-(Rational.value ⟨a,d⟩) := by
  simp [Rational.value,Signed.value_negated,neg_div]

/-- The exact returned Q decodes to the mathematical negative of the input Q. -/
theorem qn_math (code : List Function) (installed : Generated.f_qn∈code)
    (snInstalled : Generated.f_sn∈code) (smakeInstalled : Generated.f_smake∈code)
    (nzInstalled : Generated.f_nz∈code) (nuInstalled : Generated.f_nu∈code)
    (neInstalled : Generated.f_ne∈code) (keepInstalled : Generated.f_keep∈code)
    {l : PoolCalls.PoolLayout} {s : State} {cells : List (Option Value)}
    {top high mag n den d : Nat} (b : Bool)
    (context : PoolCalls.GenericPoolContext l s cells top high) (room : top<PoolCalls.capacity)
    (magLive : NatArena.Borrow s.nats mag n) (denLive : NatArena.Borrow s.nats den d)
    (positive : 0<d) :
    SourceCall Header.layout code 6 "qn" [RationalNegCalls.value mag (SignedNegCalls.bit b) den] s
        (RationalNegCalls.value mag (if n==0 then 0 else SignedNegCalls.bit (!b)) den)
        (binaryResult l s cells top high 0) ∧
    NumericRepresentation.rational s (RationalNegCalls.value mag (SignedNegCalls.bit b) den)=
      some ⟨⟨n,b⟩,d⟩ ∧
    NumericRepresentation.rational (binaryResult l s cells top high 0)
        (RationalNegCalls.value mag (if n==0 then 0 else SignedNegCalls.bit (!b)) den)=
      some ⟨Signed.negated ⟨n,b⟩,d⟩ ∧
    Rational.value ⟨Signed.negated ⟨n,b⟩,d⟩=-(Rational.value ⟨⟨n,b⟩,d⟩) := by
  exact ⟨RationalNegCalls.qn_closed code installed snInstalled smakeInstalled nzInstalled nuInstalled
    neInstalled keepInstalled b context room magLive denLive,
    NumericRepresentation.rational_value b magLive denLive positive,
    NumericRepresentation.rational_negated b (SignedNegCalls.result_borrow magLive)
      (SignedNegCalls.result_borrow denLive) positive,rational_negation _ _⟩

theorem rational_absolute (n d : Nat) (b : Bool) :
    Rational.value ⟨⟨n,false⟩,d⟩=|Rational.value ⟨⟨n,b⟩,d⟩| := by
  have nonnegative : 0≤(n:Rat)/(d:Rat) := div_nonneg (Nat.cast_nonneg n) (Nat.cast_nonneg d)
  cases b <;> simp [Rational.value,Signed.value,neg_div,abs_of_nonneg nonnegative]

/-- The source qabs result decodes to the absolute rational input value. -/
theorem qabs_math (code : List Function) (installed : Generated.f_qabs∈code)
    (smakeInstalled : Generated.f_smake∈code) (nzInstalled : Generated.f_nz∈code)
    (nuInstalled : Generated.f_nu∈code) (neInstalled : Generated.f_ne∈code)
    (keepInstalled : Generated.f_keep∈code)
    {l : PoolCalls.PoolLayout} {s : State} {cells : List (Option Value)}
    {top high mag n den d : Nat} (b : Bool)
    (context : PoolCalls.GenericPoolContext l s cells top high) (room : top<PoolCalls.capacity)
    (magLive : NatArena.Borrow s.nats mag n) (denLive : NatArena.Borrow s.nats den d)
    (positive : 0<d) :
    SourceCall Header.layout code 5 "qabs" [RationalNegCalls.value mag (SignedNegCalls.bit b) den] s
        (RationalNegCalls.value mag 0 den) (binaryResult l s cells top high 0) ∧
    NumericRepresentation.rational s (RationalNegCalls.value mag (SignedNegCalls.bit b) den)=
      some ⟨⟨n,b⟩,d⟩ ∧
    NumericRepresentation.rational (binaryResult l s cells top high 0)
        (RationalNegCalls.value mag 0 den)=some ⟨⟨n,false⟩,d⟩ ∧
    Rational.value ⟨⟨n,false⟩,d⟩=|Rational.value ⟨⟨n,b⟩,d⟩| := by
  exact ⟨RationalAbsCalls.qabs_closed code installed smakeInstalled nzInstalled nuInstalled neInstalled
    keepInstalled b context room magLive denLive,
    NumericRepresentation.rational_value b magLive denLive positive,
    NumericRepresentation.rational_value false (SignedNegCalls.result_borrow magLive)
      (SignedNegCalls.result_borrow denLive) positive,rational_absolute n d b⟩

/-- Actual point-body execution and the exact original IntervalRat singleton. -/
theorem point_math (code : List Function) (installed : Generated.f_point∈code)
    {s : State} {mag n den d : Nat} (b : Bool)
    (magLive : NatArena.Borrow s.nats mag n) (denLive : NatArena.Borrow s.nats den d)
    (positive : 0<d) :
    SourceCall Header.layout code 1 "point" [RecordCasts.rational mag (SignedNegCalls.bit b) den] s
        (IntervalCasts.value (RecordCasts.rational mag (SignedNegCalls.bit b) den)
          (RecordCasts.rational mag (SignedNegCalls.bit b) den)) s ∧
    NumericRepresentation.rational s (RecordCasts.rational mag (SignedNegCalls.bit b) den)=
      some ⟨⟨n,b⟩,d⟩ ∧
    NumericRepresentation.interval s
        (IntervalCasts.value (RecordCasts.rational mag (SignedNegCalls.bit b) den)
          (RecordCasts.rational mag (SignedNegCalls.bit b) den))=
      some (LeanCert.Core.IntervalRat.singleton (Rational.value ⟨⟨n,b⟩,d⟩)) := by
  exact ⟨RationalPointCalls.point_closed code installed magLive denLive (SignedNegCalls.bit_bound b),
    NumericRepresentation.rational_value b magLive denLive positive,
    NumericRepresentation.interval_point b magLive denLive positive⟩

end ScopedC.NumericNegationRefinement
