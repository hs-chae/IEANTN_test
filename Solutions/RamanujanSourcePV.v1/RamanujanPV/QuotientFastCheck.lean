/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import RamanujanPV.QuotientAlgorithm
namespace RamanujanPV.QuotientFastCheck
open QuotientSieve QuotientAlgorithm
set_option autoImplicit false
set_option maxHeartbeats 0
theorem checkNode_sound_local {prior : Array Node} {n : Node}
    (good : ∀(i : Nat) (m : Node), (i=n.a ∨i=n.b ∨i=n.c ∨i=n.d) →
      prior[i]?=some m →total m.p m.v=m.value)
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
          have acorrect := good n.a a (Or.inl rfl) aeq
          have bcorrect := good n.b b (Or.inr (Or.inl rfl)) beq
          have ccorrect := good n.c c (Or.inr (Or.inr (Or.inl rfl))) ceq
          have dcorrect := good n.d d (Or.inr (Or.inr (Or.inr rfl))) deq
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


/-- Read the immutable complete certificate, requiring backward references.
There is no repeated array push or final-array equality computation. -/
def checkAt (nodes : Array Node) (i : Nat) : Bool :=
  match nodes[i]? with
  | none=>false
  | some n=>decide (n.p=2 ∨n.a< i ∧n.b< i ∧n.c< i ∧n.d< i) &&checkNode nodes n

def checkFast (nodes : Array Node) : Bool :=
  (List.range nodes.size).all (checkAt nodes)

theorem checkAt_sound {nodes : Array Node} {i : Nat}
    (previous : ∀(j : Nat), j< i →∀(n : Node), nodes[j]?=some n →total n.p n.v=n.value)
    (checked : checkAt nodes i=true) {n : Node} (read : nodes[i]?=some n) :
    total n.p n.v=n.value := by
  have clauses : (n.p=2 ∨n.a< i ∧n.b< i ∧n.c< i ∧n.d< i) ∧checkNode nodes n=true := by
    simpa [checkAt,read] using checked
  rcases clauses.1 with base|refs
  · have eq : n.value=n.v-1 := by simpa [checkNode,base] using clauses.2
    rw [base,total_initial,eq]
  · apply checkNode_sound_local (checked:=clauses.2)
    intro j m ref readJ
    have lt : j< i := by rcases ref with rfl|rfl|rfl|rfl <;>omega
    exact previous j lt m readJ

theorem checkFast_sound {nodes : Array Node} (checked : checkFast nodes=true) : Good nodes := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro n read
    have index : i<nodes.size := (Array.getElem?_eq_some_iff.mp read).1
    have thisChecked : checkAt nodes i=true :=
      (List.all_eq_true.mp checked) i (List.mem_range.mpr index)
    exact checkAt_sound (fun j lower m readJ=>ih j lower m readJ) thisChecked read

theorem certificate_pi {nodes : Array Node} {i : Nat} {n : Node}
    (checked : checkFast nodes=true) (read : nodes[i]?=some n)
    (square : n.v<n.p*n.p) : Nat.primeCounting n.v=n.value := by
  have count := checkFast_sound checked i n read
  rw [total_final square] at count
  exact count

#print axioms checkNode_sound_local
#print axioms checkFast_sound
#print axioms certificate_pi
end RamanujanPV.QuotientFastCheck
