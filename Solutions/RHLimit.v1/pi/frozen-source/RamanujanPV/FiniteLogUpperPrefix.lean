/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.FiniteLogNormalize
import RamanujanPV.FiniteLogSeriesRules

namespace RamanujanPV.FiniteLogUpperPrefix
open LCMSourcePV.Witness.C LCMSourcePV.ASTLoops
open FiniteScalarMachine FiniteScalarWords FiniteScalarRules FiniteLogSeriesRules
set_option autoImplicit false
set_option maxHeartbeats 0
set_option Elab.async false

def input (n : Nat) : State := ⟨fun name=>if name="n" then some (word64 n) else none⟩
def withTwo (n : Nat) : State := ⟨FiniteScalarMachine.bind (input n).env "two" (word64 1)⟩
def initialized (n : Nat) : State := ⟨FiniteScalarMachine.bind (withTwo n).env "k" (word64 0)⟩

def guardStmt : Stmt := .branch (.binary "<" (.var "n") (.nat 2))
  (.returnStmt (.cast "uint64_t" (.nat 0))) .skip
def prefixStatements : List Stmt := [guardStmt,
  .declare [⟨"uint64_t","two",some (.nat 1)⟩],
  .declare [⟨"uint64_t","k",some (.nat 0)⟩],FiniteLogNormalize.normalization]

theorem actual_source_prefix :
    (match FiniteLogSource.upperFunction.body with
      | .sequence statements=>statements.take 4 | _=>[])=prefixStatements := rfl

lemma guard_exec {p : Prototypes} {c : Service} {n : Nat} (lower : 2≤n) (nb : n<2^64) :
    Run p c guardStmt (input n) (.continuing (input n)) := by
  have np : pure p c (input n).env 8 (.binary "<" (.var "n") (.nat 2))=
      some (WideScalar.boolean (decide (n<2))) :=
    FiniteScalarMachine.pure_binary (pure_variable (by simp [input]))
      (pure_literal (by decide +kernel))
      (FiniteCellWords.u64_signed_lt nb (w:=32) (Or.inl rfl) (by decide +kernel))
  have tested : Eval p c (.binary "<" (.var "n") (.nat 2)) (input n) (input n)
      (WideScalar.boolean (decide (n<2))) := by
    change (do return (input n,←pure p c (input n).env 8 _))=some _
    rw [np]
    rfl
  have no : ¬n<2 := by omega
  apply StmtRun.branch tested
  simpa only [FiniteCellWords.truth_boolean,no,decide_false,Bool.false_eq_true,↓reduceIte] using
    (StmtRun.skip (Eval:=Eval p c) (Declare:=Declare p c) (truth:=WideScalar.truth)
      (Scope:=Scope) (input n))

lemma two_declare {p : Prototypes} {c : Service} (n : Nat) :
    Declare p c [⟨"uint64_t","two",some (.nat 1)⟩] (input n) (withTwo n) := by rfl
lemma k_declare {p : Prototypes} {c : Service} (n : Nat) :
    Declare p c [⟨"uint64_t","k",some (.nat 0)⟩] (withTwo n) (initialized n) := by rfl

/-- The actual guard, declarations and complete normalization loop execute from
only the C argument. No intended exponent or temporary-state representation is
an input premise. -/
theorem prefix_exec {p : Prototypes} {c : Service} {n : Nat}
    (lower : 2≤n) (upper : n≤2000000000000) :
    ∃t two k,SeqRun p c prefixStatements (input n) (.continuing t) ∧
      FiniteLogNormalize.Normalized t n two k ∧ t.env "log2"=none ∧
      FiniteLogNormalize.Frame (initialized n) t := by
  have nb : n<2^64 := by norm_num at upper ⊢;omega
  obtain ⟨t,two,k,loop,post,frame⟩ := FiniteLogNormalize.normalization_exec
    (p:=p) (c:=c) (s:=initialized n) (n:=n) (two:=1) (k:=0)
    (by simp [initialized,withTwo,input,FiniteScalarMachine.bind,Function.update])
    (by simp [initialized,withTwo,FiniteScalarMachine.bind,Function.update])
    (by simp [initialized,FiniteScalarMachine.bind,Function.update])
    (by norm_num) (by omega) upper
  refine ⟨t,two,k,SeqRun.next (guard_exec lower nb)
    (SeqRun.next (StmtRun.declare (two_declare n))
    (SeqRun.next (StmtRun.declare (k_declare n))
    (SeqRun.next loop (SeqRun.nil t)))),post,?_,frame⟩
  rw [frame "log2" (by decide) (by decide)]
  simp [initialized,withTwo,input,FiniteScalarMachine.bind,Function.update]

#print axioms actual_source_prefix
#print axioms guard_exec
#print axioms prefix_exec
end RamanujanPV.FiniteLogUpperPrefix
