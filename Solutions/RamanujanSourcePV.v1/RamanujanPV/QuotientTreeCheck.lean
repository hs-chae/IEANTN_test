/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import RamanujanPV.QuotientAlgorithm
import Lean.Data.RArray
namespace RamanujanPV.QuotientTreeCheck
open QuotientSieve QuotientAlgorithm
set_option autoImplicit false
set_option maxHeartbeats 0

/-- RArray is the pinned Lean library's kernel-reducible balanced lookup
representation. This checker does not invoke its native runtime implementation. -/
noncomputable def checkRecord (nodes : Lean.RArray Node) (n : Node) : Bool :=
  if n.p=2 then n.value==n.v-1
  else if n.p<3 then false else
    let a:=nodes.get n.a
    let b:=nodes.get n.b
    let c:=nodes.get n.c
    let d:=nodes.get n.d
    decide (a.p=n.p-1 ∧a.v=n.v ∧
      b.p=n.p-1 ∧b.v=n.p-1 ∧c.p=n.p-1 ∧c.v=n.p-2 ∧
      d.p=n.p-1 ∧d.v=n.v/(n.p-1) ∧
      n.value=expected (n.p-1) n.v a.value b.value c.value d.value)

noncomputable def checkAt (nodes : Lean.RArray Node) (i : Nat) : Bool :=
  let n:=nodes.get i
  decide (n.p=2 ∨n.a< i ∧n.b< i ∧n.c< i ∧n.d< i) &&checkRecord nodes n

/-- Tail-position checking avoids constructing List.range or repeatedly
copying certificate prefixes in the Lean kernel. -/
noncomputable def checkFrom (nodes : Lean.RArray Node) : Nat→Nat→Bool
  | _,0=>true
  | i,fuel+1=>checkAt nodes i &&checkFrom nodes (i+1) fuel

theorem checkRecord_sound {nodes : Lean.RArray Node} {n : Node}
    (good : ∀j, (j=n.a ∨j=n.b ∨j=n.c ∨j=n.d) →
      total (nodes.get j).p (nodes.get j).v=(nodes.get j).value)
    (checked : checkRecord nodes n=true) : total n.p n.v=n.value := by
  unfold checkRecord at checked
  split at checked
  · rename_i base
    have eq : n.value=n.v-1 := by simpa using checked
    rw [base,total_initial,eq]
  · rename_i notBase
    split at checked
    · contradiction
    · rename_i large
      let a:=nodes.get n.a
      let b:=nodes.get n.b
      let c:=nodes.get n.c
      let d:=nodes.get n.d
      have clauses : a.p=n.p-1 ∧a.v=n.v ∧
          b.p=n.p-1 ∧b.v=n.p-1 ∧c.p=n.p-1 ∧c.v=n.p-2 ∧
          d.p=n.p-1 ∧d.v=n.v/(n.p-1) ∧
          n.value=expected (n.p-1) n.v a.value b.value c.value d.value := by
        simpa [a,b,c,d] using checked
      obtain ⟨ap,av,bp,bv,cp,cv,dp,dv,value⟩:=clauses
      have acorrect:=good n.a (Or.inl rfl)
      have bcorrect:=good n.b (Or.inr (Or.inl rfl))
      have ccorrect:=good n.c (Or.inr (Or.inr (Or.inl rfl)))
      have dcorrect:=good n.d (Or.inr (Or.inr (Or.inr rfl)))
      change total a.p a.v=a.value at acorrect
      change total b.p b.v=b.value at bcorrect
      change total c.p c.v=c.value at ccorrect
      change total d.p d.v=d.value at dcorrect
      rw [ap,av] at acorrect
      rw [bp,bv] at bcorrect
      rw [cp,cv] at ccorrect
      rw [dp,dv] at dcorrect
      have p2 : 2≤n.p-1 := by omega
      have frontier : n.p-1+1=n.p := by omega
      have prev : n.p-1-1=n.p-2 := by omega
      have recur:=total_update (v:=n.v) p2
      rw [frontier,prev,acorrect,bcorrect,ccorrect,dcorrect] at recur
      rw [value]
      exact recur

theorem checkAt_sound {nodes : Lean.RArray Node} {i : Nat}
    (previous : ∀j, j < i →total (nodes.get j).p (nodes.get j).v=(nodes.get j).value)
    (checked : checkAt nodes i=true) :
    total (nodes.get i).p (nodes.get i).v=(nodes.get i).value := by
  let n:=nodes.get i
  have clauses : (n.p=2 ∨n.a< i ∧n.b< i ∧n.c< i ∧n.d< i) ∧checkRecord nodes n=true := by
    simpa [checkAt,n] using checked
  rcases clauses.1 with base|refs
  · have eq : n.value=n.v-1 := by simpa [checkRecord,base] using clauses.2
    change total n.p n.v=n.value
    rw [base,total_initial,eq]
  · apply checkRecord_sound (checked:=clauses.2)
    intro j ref
    apply previous j
    rcases ref with rfl|rfl|rfl|rfl <;>omega

theorem checkFrom_at {nodes : Lean.RArray Node} (fuel : Nat) :
    ∀i, checkFrom nodes i fuel=true →∀j, i≤j →j< i+fuel →checkAt nodes j=true := by
  induction fuel with
  | zero=>intro i checked j low high;omega
  | succ fuel ih=>
    intro i checked j low high
    have clauses : checkAt nodes i=true ∧checkFrom nodes (i+1) fuel=true := by
      simpa [checkFrom] using checked
    by_cases eq : j=i
    · simpa [eq] using clauses.1
    · exact ih (i+1) clauses.2 j (by omega) (by omega)

theorem checkFrom_sound {nodes : Lean.RArray Node} {count : Nat}
    (checked : checkFrom nodes 0 count=true) :
    ∀i, i< count →total (nodes.get i).p (nodes.get i).v=(nodes.get i).value := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih=>
    intro bound
    have check:=checkFrom_at count 0 checked i (by omega) (by omega)
    exact checkAt_sound (fun j before=>ih j before (by omega)) check

theorem certificate_pi {nodes : Lean.RArray Node} {count i : Nat}
    (checked : checkFrom nodes 0 count=true) (index : i< count)
    (square : (nodes.get i).v<(nodes.get i).p*(nodes.get i).p) :
    Nat.primeCounting (nodes.get i).v=(nodes.get i).value := by
  have exactCount:=checkFrom_sound checked i index
  rw [total_final square] at exactCount
  exact exactCount

#print axioms checkFrom_sound
#print axioms certificate_pi
end RamanujanPV.QuotientTreeCheck
