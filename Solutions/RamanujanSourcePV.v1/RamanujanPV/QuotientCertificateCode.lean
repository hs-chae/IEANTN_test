/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Lean.Data.RArray
namespace RamanujanPV.QuotientDemandCheck
set_option autoImplicit false

def numericFactors : Nat→List Nat→Bool
  | _,[]=>true
  | first,d::ds=>decide (2≤d ∧d<first ∧first%d=0) &&numericFactors (first+1) ds

def numericExpected (q v a b c d : Nat) : Nat :=
  if b=c ∨v<q*q then a else a-(d-c)

structure Gap where
  first : Nat
  last : Nat
  factors : List Nat
  deriving Repr, DecidableEq

def checkGap (g : Gap) : Bool :=
  decide (g.first+g.factors.length=g.last) &&numericFactors g.first g.factors

/-- A tail-position finite checker; no list or prefix array is constructed. -/
def allFrom (check : Nat→Bool) : Nat→Nat→Bool
  | _,0=>true
  | i,fuel+1=>check i &&allFrom check (i+1) fuel

structure Entry where
  kind : Nat
  p : Nat
  v : Nat
  value : Nat
  a : Nat := 0
  b : Nat := 0
  c : Nat := 0
  d : Nat := 0
  ga : Nat := 0
  gb : Nat := 0
  gc : Nat := 0
  gd : Nat := 0
  deriving Repr, DecidableEq

noncomputable def checkReference (nodes : Lean.RArray Entry) (gaps : Lean.RArray Gap)
    (gapCount limit ref gapIndex stage v : Nat) : Bool :=
  let e:=nodes.get ref
  decide (ref< limit ∧e.v=v) &&
    if e.kind=2 then decide (v< stage*stage)
    else decide (e.p=stage ∨(e.p≤ stage ∧gapIndex< gapCount ∧
      (gaps.get gapIndex).first=e.p ∧stage≤(gaps.get gapIndex).last))

noncomputable def checkEntry (nodes : Lean.RArray Entry) (gaps : Lean.RArray Gap)
    (gapCount i : Nat) : Bool :=
  let n:=nodes.get i
  if n.kind=0 then decide (n.p=2 ∧n.value=n.v-1)
  else if n.kind=1 then
    decide (3≤ n.p) &&
    checkReference nodes gaps gapCount i n.a n.ga (n.p-1) n.v &&
    checkReference nodes gaps gapCount i n.b n.gb (n.p-1) (n.p-1) &&
    checkReference nodes gaps gapCount i n.c n.gc (n.p-1) (n.p-2) &&
    checkReference nodes gaps gapCount i n.d n.gd (n.p-1) (n.v/(n.p-1)) &&
    decide (n.value=numericExpected (n.p-1) n.v (nodes.get n.a).value
      (nodes.get n.b).value (nodes.get n.c).value (nodes.get n.d).value)
  else if n.kind=2 then
    checkReference nodes gaps gapCount i n.a n.ga n.p n.v &&
    decide (n.v< n.p*n.p ∧n.value=(nodes.get n.a).value)
  else false

noncomputable def checkGaps (gaps : Lean.RArray Gap) (count : Nat) : Bool :=
  allFrom (fun i=>checkGap (gaps.get i)) 0 count

noncomputable def checkEntries (nodes : Lean.RArray Entry) (gaps : Lean.RArray Gap)
    (gapCount count : Nat) : Bool :=allFrom (checkEntry nodes gaps gapCount) 0 count

end RamanujanPV.QuotientDemandCheck
namespace RamanujanPV.QuotientPackedDemand
open QuotientDemandCheck
/-- Certificate coding only. Every decoded record is still checked by the
proved arithmetic/dependency validator; no numeric field is assumed correct. -/
def field (word offset width : Nat) : Nat := (word >>> offset) % (2^width)

/-- Widths: kind2,p22,v42,value42, four references32 each, four gap indexes22
 each. Total324bits. The source program's actual arithmetic remains uint64. -/
def decode (word : Nat) : Entry :=
  ⟨field word 0 2,field word 2 22,field word 24 42,field word 66 42,
    field word 108 32,field word 140 32,field word 172 32,field word 204 32,
    field word 236 22,field word 258 22,field word 280 22,field word 302 22⟩

/-- Lazy structural decoding preserves balanced kernel lookup. It does not
construct an immutable Array/List and introduces no execution trust premise. -/
def unpack : Lean.RArray Nat→Lean.RArray Entry
  | .leaf word=>.leaf (decode word)
  | .branch pivot left right=>.branch pivot (unpack left) (unpack right)

end RamanujanPV.QuotientPackedDemand
