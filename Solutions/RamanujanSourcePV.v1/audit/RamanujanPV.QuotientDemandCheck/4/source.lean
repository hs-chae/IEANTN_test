/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import RamanujanPV.QuotientTreeCheck
import RamanujanPV.QuotientCertificateCode
namespace RamanujanPV.QuotientDemandCheck
open QuotientSieve QuotientAlgorithm
set_option autoImplicit false
set_option maxHeartbeats 0

theorem numericFactors_eq (first : Nat) (factors : List Nat) :
    numericFactors first factors=QuotientSieve.checkFactors first factors := by
  induction factors generalizing first with
  | nil=>rfl
  | cons d ds ih=>simp [numericFactors,QuotientSieve.checkFactors,ih]

theorem numericExpected_eq (q v a b c d : Nat) :
    numericExpected q v a b c d=QuotientAlgorithm.expected q v a b c d := rfl

def GapMeaning (g : Gap) : Prop :=
  ∀q, g.first≤ q →q< g.last →¬Nat.Prime q

theorem checkGap_sound {g : Gap} (checked : checkGap g=true) : GapMeaning g := by
  have clauses : g.first+g.factors.length=g.last ∧checkFactors g.first g.factors=true := by
    simpa [checkGap,numericFactors_eq] using checked
  intro q low high
  exact checkFactors_sound g.first g.factors clauses.2 q low (by omega)

theorem allFrom_at {check : Nat→Bool} (fuel : Nat) :
    ∀i, allFrom check i fuel=true →∀j, i≤ j →j< i+fuel →check j=true := by
  induction fuel with
  | zero=>intro i checked j low high;omega
  | succ fuel ih=>
    intro i checked j low high
    have clauses : check i=true ∧allFrom check (i+1) fuel=true := by simpa [allFrom] using checked
    by_cases eq : j=i
    · simpa [eq] using clauses.1
    · exact ih (i+1) clauses.2 j (by omega) (by omega)

/-- Independent numerical chunks compose without reevaluating their contents. -/
theorem allFrom_append (check : Nat→Bool) (n m : Nat) :
    ∀i, allFrom check i (n+m)=(allFrom check i n &&allFrom check (i+n) m) := by
  induction n with
  | zero=>intro i;simp [allFrom]
  | succ n ih=>intro i;simp [allFrom,Nat.succ_add,ih,Nat.add_assoc,Bool.and_assoc]

theorem allFrom_append_checked {check : Nat→Bool} {i n m : Nat}
    (left : allFrom check i n=true) (right : allFrom check (i+n) m=true) :
    allFrom check i (n+m)=true := by
  rw [allFrom_append]
  simp [left,right]

/-- kind0: initialized S2; kind1: recurrence S(p,v); kind2: final actual pi. -/
def Meaning (e : Entry) : Prop :=
  if e.kind=2 then Nat.primeCounting e.v=e.value else total e.p e.v=e.value

theorem reference_sound {nodes : Lean.RArray Entry} {gaps : Lean.RArray Gap}
    {gapCount limit ref gapIndex stage v : Nat}
    (gapGood : ∀g, g< gapCount →GapMeaning (gaps.get g))
    (previous : ∀j, j< limit →Meaning (nodes.get j))
    (checked : checkReference nodes gaps gapCount limit ref gapIndex stage v=true) :
    total stage v=(nodes.get ref).value := by
  let e:=nodes.get ref
  have both : (ref< limit ∧e.v=v) ∧
      (if e.kind=2 then decide (v< stage*stage)
       else decide (e.p=stage ∨(e.p≤ stage ∧gapIndex< gapCount ∧
         (gaps.get gapIndex).first=e.p ∧stage≤(gaps.get gapIndex).last)))=true := by
    simpa [checkReference,e] using checked
  have known:=previous ref both.1.1
  change Meaning e at known
  by_cases final : e.kind=2
  · have square : v< stage*stage := by simpa [final] using both.2
    have count : Nat.primeCounting v=e.value := by simpa [Meaning,final,both.1.2] using known
    exact use_finished square count
  · have count : total e.p v=e.value := by simpa [Meaning,final,both.1.2] using known
    have alternatives : e.p=stage ∨(e.p≤ stage ∧gapIndex< gapCount ∧
        (gaps.get gapIndex).first=e.p ∧stage≤(gaps.get gapIndex).last) := by
      simpa [final] using both.2
    rcases alternatives with same|⟨order,index,first,last⟩
    · simpa [same] using count
    · have gap:=gapGood gapIndex index
      have jump : total e.p v=total stage v := by
        apply total_jump order
        intro q low high
        exact gap q (by simpa [first] using low) (high.trans_le last)
      exact jump.symm.trans count

theorem entry_sound {nodes : Lean.RArray Entry} {gaps : Lean.RArray Gap} {gapCount i : Nat}
    (gapGood : ∀g, g< gapCount →GapMeaning (gaps.get g))
    (previous : ∀j, j< i →Meaning (nodes.get j))
    (checked : checkEntry nodes gaps gapCount i=true) : Meaning (nodes.get i) := by
  let n:=nodes.get i
  change Meaning n
  by_cases base : n.kind=0
  · have fields : n.p=2 ∧n.value=n.v-1 := by simpa [checkEntry,n,base] using checked
    have notFinal : n.kind≠2 := by omega
    simp only [Meaning,if_neg notFinal,fields.1,total_initial,fields.2]
  · by_cases step : n.kind=1
    · have clauses : 3≤ n.p ∧
          checkReference nodes gaps gapCount i n.a n.ga (n.p-1) n.v=true ∧
          checkReference nodes gaps gapCount i n.b n.gb (n.p-1) (n.p-1)=true ∧
          checkReference nodes gaps gapCount i n.c n.gc (n.p-1) (n.p-2)=true ∧
          checkReference nodes gaps gapCount i n.d n.gd (n.p-1) (n.v/(n.p-1))=true ∧
          n.value=expected (n.p-1) n.v (nodes.get n.a).value
            (nodes.get n.b).value (nodes.get n.c).value (nodes.get n.d).value := by
        simpa [checkEntry,n,base,step,and_assoc,numericExpected_eq] using checked
      obtain ⟨p3,ac,bc,cc,dc,arithmetic⟩:=clauses
      have a:=reference_sound gapGood previous ac
      have b:=reference_sound gapGood previous bc
      have c:=reference_sound gapGood previous cc
      have d:=reference_sound gapGood previous dc
      have prev : n.p-1-1=n.p-2 := by omega
      rw [←prev] at c
      have result:=local_step (p:=n.p-1) (v:=n.v) (y:=n.value) (by omega) a b c d arithmetic.symm
      have frontier : n.p-1+1=n.p := by omega
      have notFinal : n.kind≠2 := by omega
      simpa [Meaning,notFinal,frontier] using result
    · by_cases final : n.kind=2
      · have clauses : checkReference nodes gaps gapCount i n.a n.ga n.p n.v=true ∧
            n.v< n.p*n.p ∧n.value=(nodes.get n.a).value := by
          simpa [checkEntry,n,base,step,final,and_assoc] using checked
        have known:=reference_sound gapGood previous clauses.1
        have result:=finish_value clauses.2.1 known
        simpa [Meaning,final,clauses.2.2] using result
      · simp [checkEntry,n,base,step,final] at checked

theorem gaps_sound {gaps : Lean.RArray Gap} {count : Nat} (checked : checkGaps gaps count=true) :
    ∀g, g< count →GapMeaning (gaps.get g) := by
  intro g bound
  exact checkGap_sound (allFrom_at count 0 checked g (by omega) (by omega))

theorem entries_sound {nodes : Lean.RArray Entry} {gaps : Lean.RArray Gap} {gapCount count : Nat}
    (gapChecked : checkGaps gaps gapCount=true) (checked : checkEntries nodes gaps gapCount count=true) :
    ∀i, i< count →Meaning (nodes.get i) := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih=>
    intro bound
    have check:=allFrom_at count 0 checked i (by omega) (by omega)
    exact entry_sound (gaps_sound gapChecked) (fun j before=>ih j before (by omega)) check

theorem certificate_pi {nodes : Lean.RArray Entry} {gaps : Lean.RArray Gap} {gapCount count i : Nat}
    (gapChecked : checkGaps gaps gapCount=true) (checked : checkEntries nodes gaps gapCount count=true)
    (index : i< count) (final : (nodes.get i).kind=2) :
    Nat.primeCounting (nodes.get i).v=(nodes.get i).value := by
  have known:=entries_sound gapChecked checked i index
  simpa [Meaning,final] using known

#print axioms reference_sound
#print axioms entries_sound
#print axioms certificate_pi
end RamanujanPV.QuotientDemandCheck
