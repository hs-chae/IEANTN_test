/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedC.RationalIntervalNegBody
import ScopedC.NumericNegationRefinement

namespace ScopedC.NumericIntervalNegRefinement
open ScopedC.Syntax ScopedC.Machine ScopedC.SourceCalls
open ScopedC.RationalInputs
open ScopedNumerical LeanCert.Core
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem negative_value (q : Data) : q.negativeMath.value=-q.mathematical.value :=
  NumericNegationRefinement.rational_negation _ _

/-- Source RI decoding follows the original rational interval invariant. -/
theorem decoded_interval {s : State} {lo hi : Data}
    (hl : lo.Live s) (hh : hi.Live s) (lp : 0<lo.denominator) (hp : 0<hi.denominator)
    (ordered : lo.mathematical.value≤hi.mathematical.value) :
    NumericRepresentation.interval s (RationalIntervalNegCalls.value lo hi)=
      some (⟨lo.mathematical.value,hi.mathematical.value,ordered⟩ : IntervalRat) := by
  have dl := Data.decoded hl lp
  have dh := Data.decoded hh hp
  simp [NumericRepresentation.interval,RationalIntervalNegCalls.value,IntervalCasts.value,dl,dh,ordered]

theorem decoded_negative_interval {s : State} {lo hi : Data}
    (hl : lo.Live s) (hh : hi.Live s) (lp : 0<lo.denominator) (hp : 0<hi.denominator)
    (ordered : lo.mathematical.value≤hi.mathematical.value) :
    NumericRepresentation.interval s (RationalIntervalNegCalls.result lo hi)=
      some (IntervalRat.neg ⟨lo.mathematical.value,hi.mathematical.value,ordered⟩) := by
  have dl := Data.negative_decoded hl lp
  have dh := Data.negative_decoded hh hp
  simp [NumericRepresentation.interval,RationalIntervalNegCalls.result,IntervalCasts.value,dl,dh,
    negative_value,IntervalRat.neg,neg_le_neg_iff,ordered]

/-- Actual source body, decoded input, and decoded exact original interval
negation. The order and positive-denominator premises are input-domain facts. -/
theorem rneg_math (code : List Function) (installed : Generated.f_rneg∈code)
    (qnInstalled : Generated.f_qn∈code) (snInstalled : Generated.f_sn∈code)
    (smakeInstalled : Generated.f_smake∈code) (nzInstalled : Generated.f_nz∈code)
    (nuInstalled : Generated.f_nu∈code) (neInstalled : Generated.f_ne∈code)
    (keepInstalled : Generated.f_keep∈code)
    {l : PoolCalls.PoolLayout} {s : State} {cells : List (Option Value)} {top high : Nat}
    (lo hi : Data) (loLive : lo.Live s) (hiLive : hi.Live s)
    (loPositive : 0<lo.denominator) (hiPositive : 0<hi.denominator)
    (ordered : lo.mathematical.value≤hi.mathematical.value)
    (context : PoolCalls.GenericPoolContext l s cells top high) (room : top+1<PoolCalls.capacity) :
    SourceCall Header.layout code 7 "rneg" [RationalIntervalNegCalls.value lo hi] s
        (RationalIntervalNegCalls.result lo hi) (RationalIntervalNegCalls.rnegResult l s cells top high) ∧
    NumericRepresentation.interval s (RationalIntervalNegCalls.value lo hi)=
      some (⟨lo.mathematical.value,hi.mathematical.value,ordered⟩ : IntervalRat) ∧
    NumericRepresentation.interval (RationalIntervalNegCalls.rnegResult l s cells top high)
        (RationalIntervalNegCalls.result lo hi)=
      some (IntervalRat.neg ⟨lo.mathematical.value,hi.mathematical.value,ordered⟩) := by
  refine ⟨RationalIntervalNegCalls.rneg_closed code installed qnInstalled snInstalled smakeInstalled
    nzInstalled nuInstalled neInstalled keepInstalled lo hi loLive hiLive context room,
    decoded_interval loLive hiLive loPositive hiPositive ordered,?_⟩
  have loAfter : lo.Live (RationalIntervalNegCalls.rnegResult l s cells top high) :=
    Data.live_after (Data.live_after loLive)
  have hiAfter : hi.Live (RationalIntervalNegCalls.rnegResult l s cells top high) :=
    Data.live_after (Data.live_after hiLive)
  exact decoded_negative_interval loAfter hiAfter loPositive hiPositive ordered

end ScopedC.NumericIntervalNegRefinement
