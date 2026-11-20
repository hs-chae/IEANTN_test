/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import RamanujanPV.QuotientSieve
namespace RamanujanPV.QuotientAlgorithm
open QuotientSieve
set_option autoImplicit false
set_option maxHeartbeats 0

def update (p : Nat) (old : Nat→Nat) (v : Nat) : Nat :=
  if old p=old (p-1) ∨v<p*p then old v
  else old v-(old (v/p)-old (p-1))

def table : Nat→Nat→Nat
  | 0 => fun v=>v-1
  | k+1 => update (k+2) (table k)

theorem table_correct (k v : Nat) : table k v=total (k+2) v := by
  induction k generalizing v with
  | zero => simpa [table] using (total_initial v).symm
  | succ k ih =>
    simp only [table,update,ih]
    simpa [Nat.add_assoc] using (total_update (p:=k+2) (v:=v) (by omega)).symm

/-- Fully specified quotient recurrence; no supplied pi values. It is a
mathematical program specification, not the optimized C memory algorithm. -/
def count (n : Nat) : Nat := if n<2 then 0 else table (n.sqrt-1) n

theorem count_correct (n : Nat) : count n=Nat.primeCounting n := by
  unfold count
  split
  · rename_i small
    have : n=0 ∨n=1 := by omega
    rcases this with rfl|rfl <;> simp
  · rename_i large
    have root : 1≤n.sqrt := (Nat.le_sqrt).mpr (by omega : 1*1≤n)
    rw [table_correct]
    have frontier : n.sqrt-1+2=n.sqrt+1 := by omega
    rw [frontier]
    exact total_final (Nat.lt_succ_sqrt n)

/-- Each node claims a survivor count, not an assumed prime-count entry.
All references must be to already accepted nodes. -/
structure Node where
  p : Nat
  v : Nat
  value : Nat
  a : Nat := 0
  b : Nat := 0
  c : Nat := 0
  d : Nat := 0
  deriving Repr,DecidableEq

def expected (q v a b c d : Nat) : Nat :=
  if b=c ∨v<q*q then a else a-(d-c)

def checkNode (prior : Array Node) (n : Node) : Bool :=
  if n.p=2 then n.value==n.v-1
  else if n.p<3 then false else
    match prior[n.a]?,prior[n.b]?,prior[n.c]?,prior[n.d]? with
    | some a,some b,some c,some d =>
      decide (a.p=n.p-1 ∧a.v=n.v ∧
        b.p=n.p-1 ∧b.v=n.p-1 ∧
        c.p=n.p-1 ∧c.v=n.p-2 ∧
        d.p=n.p-1 ∧d.v=n.v/(n.p-1) ∧
        n.value=expected (n.p-1) n.v a.value b.value c.value d.value)
    | _,_,_,_ =>false

def Good (nodes : Array Node) : Prop :=
  ∀(i : Nat) (n : Node), nodes[i]?=some n →total n.p n.v=n.value

theorem checkNode_sound {prior : Array Node} {n : Node} (good : Good prior)
    (checked : checkNode prior n=true) : total n.p n.v=n.value := by
  unfold checkNode at checked
  split at checked
  · rename_i base
    have value : n.value=n.v-1 := by simpa using checked
    rw [base,total_initial,value]
  · rename_i notBase
    split at checked
    · contradiction
    · rename_i large
      cases aeq : prior[n.a]? with
      | none => simp [aeq] at checked
      | some a =>
       cases beq : prior[n.b]? with
       | none => simp [aeq,beq] at checked
       | some b =>
        cases ceq : prior[n.c]? with
        | none => simp [aeq,beq,ceq] at checked
        | some c =>
         cases deq : prior[n.d]? with
         | none => simp [aeq,beq,ceq,deq] at checked
         | some d =>
          have fields : a.p=n.p-1 ∧a.v=n.v ∧
              b.p=n.p-1 ∧b.v=n.p-1 ∧
              c.p=n.p-1 ∧c.v=n.p-2 ∧
              d.p=n.p-1 ∧d.v=n.v/(n.p-1) ∧
              n.value=expected (n.p-1) n.v a.value b.value c.value d.value := by
            simpa [aeq,beq,ceq,deq] using checked
          obtain ⟨ap,av,bp,bv,cp,cv,dp,dv,value⟩ := fields
          have acorrect := good n.a a aeq
          have bcorrect := good n.b b beq
          have ccorrect := good n.c c ceq
          have dcorrect := good n.d d deq
          rw [ap,av] at acorrect
          rw [bp,bv] at bcorrect
          rw [cp,cv] at ccorrect
          rw [dp,dv] at dcorrect
          have p2 : 2≤n.p-1 := by omega
          have frontier : n.p-1+1=n.p := by omega
          have prev : n.p-1-1=n.p-2 := by omega
          have recur := total_update (v:=n.v) p2
          rw [frontier,prev,acorrect,bcorrect,ccorrect,dcorrect] at recur
          rw [value]
          exact recur

theorem good_empty : Good #[] := by simp [Good]

theorem good_push {prior : Array Node} {n : Node} (good : Good prior)
    (checked : checkNode prior n=true) : Good (prior.push n) := by
  intro i m read
  by_cases before : i<prior.size
  · have old : prior[i]?=some m := by simpa [Array.getElem?_push,before,show i≠prior.size by omega] using read
    exact good i m old
  · have eq : i=prior.size := by
      have inRange := (Array.getElem?_eq_some_iff.mp read).1
      simp only [Array.size_push] at inRange
      omega
    subst i
    have value : n=m := by simpa using read
    subst m
    exact checkNode_sound good checked

/-- Sequential acceptance; each new entry can reference only the existing
prefix. Array bounds are checked by the actual optional lookups. -/
def checkAll (prior : Array Node) : List Node→Option (Array Node)
  | [] => some prior
  | n::ns => if checkNode prior n then checkAll (prior.push n) ns else none

theorem checkAll_sound (nodes : List Node) :
    ∀prior final, Good prior →checkAll prior nodes=some final →Good final := by
  induction nodes with
  | nil =>
    intro prior final good checked
    have eq : prior=final := by simpa [checkAll] using checked
    simpa [←eq] using good
  | cons n ns ih =>
    intro prior final good checked
    by_cases localCheck : checkNode prior n=true
    · exact ih (prior.push n) final (good_push good localCheck) (by simpa [checkAll,localCheck] using checked)
    · simp [checkAll,localCheck] at checked

/-- This is the exact completed numerical target of a certificate. It
requires actual accepted checker execution, not a process return0 receipt. -/
theorem certificate_pi {nodes : List Node} {final : Array Node} {i : Nat} {n : Node}
    (checked : checkAll #[] nodes=some final) (read : final[i]?=some n)
    (square : n.v<n.p*n.p) : Nat.primeCounting n.v=n.value := by
  have good := checkAll_sound nodes #[] final good_empty checked
  have exactCount := good i n read
  rw [total_final square] at exactCount
  exact exactCount

/-- Constant-size proof-producing local arithmetic: named preceding theorems
supply exact count identities; only the closed integer arithmetic is reduced.
This avoids reducing or comparing a huge persistent prefix array in the kernel. -/
theorem local_step {p v av bv cv dv y : Nat} (hp : 2≤p)
    (a : total p v=av) (b : total p p=bv) (c : total p (p-1)=cv)
    (d : total p (v/p)=dv) (arithmetic : expected p v av bv cv dv=y) :
    total (p+1) v=y := by
  rw [total_update hp,a,b,c,d]
  exact arithmetic

#print axioms local_step
#print axioms checkAll_sound
#print axioms certificate_pi
#print axioms count_correct
#print axioms checkNode_sound
#print axioms good_push
end RamanujanPV.QuotientAlgorithm
