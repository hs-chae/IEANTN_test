/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedC.NumericDyadicNegRefinement

namespace ScopedC.DyadicValueEquivalence
open ScopedC.Syntax ScopedC.Machine ScopedC.SourceCalls
open ScopedC.DyadicRepresentation
open LeanCert.Core
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Endpoint values, not exponent/mantissa fields, are the representation
contract when the original algorithm retains an equivalent coarser dyadic. -/
def SameValues (a b : IntervalDyadic) : Prop :=
  a.lo.toRat=b.lo.toRat ∧ a.hi.toRat=b.hi.toRat

theorem same_refl (a : IntervalDyadic) : SameValues a a := ⟨rfl,rfl⟩
theorem same_symm {a b : IntervalDyadic} (h : SameValues a b) : SameValues b a :=
  ⟨h.1.symm,h.2.symm⟩
theorem same_trans {a b c : IntervalDyadic} (ab : SameValues a b) (bc : SameValues b c) : SameValues a c :=
  ⟨ab.1.trans bc.1,ab.2.trans bc.2⟩

theorem neg_same {a b : IntervalDyadic} (h : SameValues a b) :
    SameValues (IntervalDyadic.neg a) (IntervalDyadic.neg b) := by
  constructor
  · simpa only [IntervalDyadic.neg,LeanCert.Core.Dyadic.toRat_neg] using congrArg Neg.neg h.2
  · simpa only [IntervalDyadic.neg,LeanCert.Core.Dyadic.toRat_neg] using congrArg Neg.neg h.1

theorem toIntervalRat_eq {a b : IntervalDyadic} (h : SameValues a b) :
    a.toIntervalRat=b.toIntervalRat := by
  cases a
  cases b
  simp only [IntervalDyadic.toIntervalRat,IntervalRat.mk.injEq]
  exact h

theorem zero_same (old : IntervalDyadic) (lo : old.lo.toRat=0) (hi : old.hi.toRat=0) :
    SameValues (words100 0 0 (by decide)) old := by
  constructor
  · rw [lo]
    simp [words100,LeanCert.Core.Dyadic.toRat]
  · rw [hi]
    simp [words100,LeanCert.Core.Dyadic.toRat]

/-- A source record may represent an old interval with different stored
exponents, provided both endpoints have exactly equal rational values. -/
def Represents (s : State) (v : Value) (old : IntervalDyadic) (ok : Bool) : Prop :=
  ∃ canonical,interval s v=some (canonical,ok) ∧ SameValues canonical old

/-- The exact old negation is preserved for every semantically equal old input,
including its harmless coarser zero representation. -/
theorem source_neg_rep (code : List Function) (installed : Generated.f_ineg∈code)
    (snInstalled : Generated.f_sn∈code) (smakeInstalled : Generated.f_smake∈code)
    (nzInstalled : Generated.f_nz∈code) (nuInstalled : Generated.f_nu∈code)
    (neInstalled : Generated.f_ne∈code) (keepInstalled : Generated.f_keep∈code)
    {l : PoolCalls.PoolLayout} {s : State} {cells : List (Option Value)} {top high : Nat}
    (lo hi : Endpoint) (ok : Bool) (loLive : lo.Live s) (hiLive : hi.Live s)
    (ordered : lo.mathematical.value≤hi.mathematical.value)
    (old : IntervalDyadic) (same : SameValues (words100 lo.mathematical.value hi.mathematical.value ordered) old)
    (context : PoolCalls.GenericPoolContext l s cells top high) (room : top+1<PoolCalls.capacity) :
    SourceCall Header.layout code 6 "ineg" [DyadicIntervalNegCalls.value lo hi ok] s
        (DyadicIntervalNegCalls.result lo hi ok) (DyadicIntervalNegCalls.inegResult l s cells top high) ∧
    Represents (DyadicIntervalNegCalls.inegResult l s cells top high) (DyadicIntervalNegCalls.result lo hi ok)
      (IntervalDyadic.neg old) ok := by
  have h := NumericDyadicNegRefinement.ineg_math code installed snInstalled smakeInstalled nzInstalled
    nuInstalled neInstalled keepInstalled lo hi ok loLive hiLive ordered context room
  exact ⟨h.1,_,h.2.2,neg_same same⟩

end ScopedC.DyadicValueEquivalence
