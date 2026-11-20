/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import RamanujanPV.QuotientCMachine
import RamanujanPV.QuotientCSource
namespace RamanujanPV.QuotientSqrtExecute
open LCMSourcePV.Witness.C QuotientCMachine
set_option autoImplicit false
set_option maxHeartbeats 0

def noCalls : Service := fun _ _=>none

def condition : Expr := .binary "<=" (.binary "+" (.var "r") (.nat 1))
  (.binary "/" (.var "n") (.binary "+" (.var "r") (.nat 1)))
def iteration : Stmt := .sequence [.eval (.unary "++" (.var "r"))]
def input (n : Nat) (heap : Heap) : State := ⟨QuotientCMachine.bind emptyEnv "n" (.u64 n),heap⟩

theorem source_shape : QuotientCSource.sqrtFunction.body=
    .sequence [.declare [⟨"uint64_t","r",some (.nat 0)⟩],
      .whileLoop condition iteration,.returnStmt (.var "r")] := rfl

theorem increment_word {n r : Nat} (bound : n≤2000000000000) (before : r≤n.sqrt) :
    r+1< modulus := by
  have root := Nat.sqrt_le_self n
  norm_num [modulus] at *
  omega

theorem condition_eval {n r : Nat} (bound : n≤2000000000000) (before : r≤n.sqrt)
    (s : State) (readN : s.env "n"=some (.u64 n)) (readR : s.env "r"=some (.u64 r)) :
    Eval noCalls condition s s (.i32 (if r<n.sqrt then 1 else 0)) := by
  have word := increment_word bound before
  have nword : n< modulus := by norm_num [modulus];omega
  have divWord : n/(r+1)< modulus := (Nat.div_le_self _ _).trans_lt nword
  have quotientGuard : r+1≤n/(r+1) ↔r<n.sqrt := by
    rw [Nat.le_div_iff_mul_le (by omega : 0<r+1),←Nat.le_sqrt]
    omega
  simp [Eval,eval,evalPure,condition,literal,readN,readR,binary,
    Value.scalar,packArithmetic,unsignedCommon,word,Nat.mod_eq_of_lt word,
    Nat.mod_eq_of_lt divWord,quotientGuard]

theorem close_existing_update (s : State) (name : String) (old new : Value)
    (present : s.env name=some old) :
    closeScope s {s with env:=QuotientCMachine.bind s.env name new}={s with env:=QuotientCMachine.bind s.env name new} := by
  cases s with
  | mk env heap =>
    change env name=some old at present
    simp only [closeScope]
    congr 1
    funext key
    by_cases eq : key=name
    · subst key
      simp [present,QuotientCMachine.bind]
    · cases h : env key <;>simp [QuotientCMachine.bind,eq,h]

theorem while_refines (n : Nat) (bound : n≤2000000000000) :
    ∀fuel r, r≤n.sqrt →n.sqrt<r+fuel →
      ∀s : State, s.env "n"=some (.u64 n) →s.env "r"=some (.u64 r) →
      ∃t, WhileRun noCalls condition iteration s (.continuing t) ∧
        t.env "r"=some (.u64 n.sqrt) ∧t.heap=s.heap := by
  intro fuel
  induction fuel with
  | zero => intro r before budget;omega
  | succ fuel ih =>
    intro r before budget s readN readR
    by_cases advance : r<n.sqrt
    · let next : State := {s with env:=QuotientCMachine.bind s.env "r" (.u64 (r+1))}
      have word := increment_word bound before
      have increment : Eval noCalls (.unary "++" (.var "r")) s next (.u64 (r+1)) := by
        simp [Eval,eval,readR,next,Nat.mod_eq_of_lt word]
      have nextN : next.env "n"=some (.u64 n) := by simp [next,readN]
      have nextR : next.env "r"=some (.u64 (r+1)) := by simp [next]
      obtain ⟨t,rest,done,heap⟩ := ih (r+1) (by omega) (by omega) next nextN nextR
      refine ⟨t,?_,done,heap⟩
      apply LCMSourcePV.ASTLoops.WhileRun.next (condition_eval bound before s readN readR)
      · simp [truth,advance,Value.bits]
      · apply LCMSourcePV.ASTLoops.StmtRun.sequence
          (LCMSourcePV.ASTLoops.SeqRun.next
            (LCMSourcePV.ASTLoops.StmtRun.evaluate increment) (LCMSourcePV.ASTLoops.SeqRun.nil next))
        change .continuing next=closeFlow s (.continuing next)
        simp only [closeFlow]
        rw [close_existing_update s "r" (.u64 r) (.u64 (r+1)) readR]
      · exact rest
    · have same : r=n.sqrt := by omega
      refine ⟨s,?_,?_,rfl⟩
      · apply LCMSourcePV.ASTLoops.WhileRun.done (condition_eval bound before s readN readR)
        simp [truth,advance,Value.bits]
      · simpa [same] using readR

/-- Entire actual isqrt source body: local initialization, every guarded
increment, correct lexical block exit and the actual returned uint64 value. -/
theorem function_refines (n : Nat) (bound : n≤2000000000000) (heap : Heap) :
    ∃t, Run noCalls QuotientCSource.sqrtFunction.body (input n heap)
      (.returned t (.u64 n.sqrt)) ∧t.heap=heap := by
  let initial := input n heap
  let started : State := {initial with env:=QuotientCMachine.bind initial.env "r" (.u64 0)}
  have declaration : Declare noCalls [⟨"uint64_t","r",some (.nat 0)⟩] initial started := by
    simp [Declare,declare,List.foldlM,evalPure,literal,initial,input,QuotientCMachine.bind,emptyEnv,
      uint64,Value.scalar,started,modulus]
  obtain ⟨t,loop,read,heapEq⟩ := while_refines n bound (n.sqrt+1) 0 (by omega) (by omega) started
    (by simp [started,initial,input]) (by simp [started])
  let final := closeScope initial t
  refine ⟨final,?_,heapEq⟩
  rw [source_shape]
  apply LCMSourcePV.ASTLoops.StmtRun.sequence (inner:=.returned t (.u64 n.sqrt))
  · apply LCMSourcePV.ASTLoops.SeqRun.next (LCMSourcePV.ASTLoops.StmtRun.declare declaration)
    apply LCMSourcePV.ASTLoops.SeqRun.next (LCMSourcePV.ASTLoops.StmtRun.whileLoop loop)
    apply LCMSourcePV.ASTLoops.SeqRun.returned
    apply LCMSourcePV.ASTLoops.StmtRun.returnValue
    simp [Eval,eval,evalPure,read]
  · rfl

/-- The optimized count program's only modular helper service. Each supported
response is refined to the source-bound sqrt body, never a correctness oracle. -/
def service : Service := fun name args =>
  if name="rpc_isqrt" then match args with
    | [.u64 n] => if n≤2000000000000 then some (.u64 n.sqrt) else none
    | _=>none
  else none

theorem service_closed {name : String} {args : List Value} {result : Value}
    (run : service name args=some result) (heap : Heap) :
    ∃n, name="rpc_isqrt" ∧args=[.u64 n] ∧n≤2000000000000 ∧
      ∃t, Run noCalls QuotientCSource.sqrtFunction.body (input n heap)
        (.returned t result) ∧t.heap=heap := by
  by_cases nameEq : name="rpc_isqrt"
  · subst name
    cases args with
    | nil => simp [service] at run
    | cons a rest =>
      cases rest with
      | cons b bs => simp [service] at run
      | nil =>
        cases a with
        | i32 n | i64 n | ptr n => simp [service] at run
        | u64 n =>
          by_cases bound : n≤2000000000000
          · have eq : .u64 n.sqrt=result := by simpa [service,bound] using run
            subst result
            exact ⟨n,rfl,rfl,bound,function_refines n bound heap⟩
          · simp [service,bound] at run
  · simp [service,nameEq] at run

#print axioms condition_eval
#print axioms function_refines
#print axioms service_closed
end RamanujanPV.QuotientSqrtExecute
