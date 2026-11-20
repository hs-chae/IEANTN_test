/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import RamanujanPV.QuotientCMachine
import RamanujanPV.QuotientCSourceV2
import RamanujanPV.QuotientTables
import RamanujanPV.QuotientWordBounds

/-! Actual source-AST and memory refinement for the efficient quotient sieve.
This module must not be described as completed PV of a whole native count until
its complete function/loop execution and a concrete accepted run are connected. -/
namespace RamanujanPV.QuotientCExecute
open LCMSourcePV.Witness.C
open RamanujanPV.QuotientCMachine
open RamanujanPV.QuotientTables
set_option autoImplicit false
set_option maxHeartbeats 2000000

private def var (s : String) : Expr := .var s
private def index (s : String) (i : Expr) : Expr := .index (.var s) i
private def bin (op : String) (a b : Expr) : Expr := .binary op a b
private def subBefore : Expr := bin "-" (var "sub") (var "before")

def largeBody : Stmt := .sequence [
  .declare [⟨"uint64_t","ip",some (bin "*" (var "i") (var "p"))⟩],
  .declare [⟨"uint64_t","sub",some (.nat 0)⟩],
  .branch (bin "<=" (var "ip") (var "r"))
    (.eval (bin "=" (var "sub") (index "large" (var "ip"))))
    (.eval (bin "=" (var "sub") (index "small" (bin "/" (var "n") (var "ip"))))),
  .branch (bin "<" (var "sub") (var "before")) (.returnStmt (.nat 0)) .skip,
  .branch (bin "<" (index "large" (var "i")) subBefore) (.returnStmt (.nat 0)) .skip,
  .eval (bin "=" (index "large" (var "i")) (bin "-" (index "large" (var "i")) subBefore))]

def smallBody : Stmt := .sequence [
  .declare [⟨"uint64_t","sub",some (index "small" (bin "/" (var "v") (var "p")))⟩],
  .branch (bin "<" (var "sub") (var "before")) (.returnStmt (.nat 0)) .skip,
  .branch (bin "<" (index "small" (var "v")) subBefore) (.returnStmt (.nat 0)) .skip,
  .eval (bin "=" (index "small" (var "v")) (bin "-" (index "small" (var "v")) subBefore)),
  .eval (.unary "--" (var "v"))]

private def seqAt (s : Stmt) (i : Nat) : Option Stmt := match s with
  | .sequence body => body[i]?
  | _ => none
private def forBody : Stmt → Option Stmt
  | .forLoop _ _ _ body => some body
  | _ => none
private def noBranch : Stmt → Option Stmt
  | .branch _ _ no => some no
  | _ => none
private def yesBranch : Stmt → Option Stmt
  | .branch _ yes _ => some yes
  | _ => none
private def whileBody : Stmt → Option Stmt
  | .whileLoop _ body => some body
  | _ => none

def actualLargeBody : Option Stmt := do
  let outer ← seqAt RamanujanPV.QuotientCSourceV2.countFunction.body 5
  let branch ← forBody outer
  let active ← noBranch branch
  let loop ← seqAt active 3
  forBody loop

def actualSmallBody : Option Stmt := do
  let outer ← seqAt RamanujanPV.QuotientCSourceV2.countFunction.body 5
  let branch ← forBody outer
  let active ← noBranch branch
  let test ← seqAt active 5
  let yes ← yesBranch test
  let loop ← seqAt yes 1
  whileBody loop

/-- Exact subtrees of the already byte-linked C AST, not independently invented
complete-function interpretations. -/
theorem actual_large_body : actualLargeBody=some largeBody := rfl
theorem actual_small_body : actualSmallBody=some smallBody := rfl

/-- Every expression in BOTH complete byte-linked source functions has depth
at most4. The generic expression allowance8 therefore covers all selected syntax;
its failure-at-zero rule has not been replaced with a fabricated success. -/
theorem actual_source_expression_depth :
    stmtWithin 4 32 RamanujanPV.QuotientCSourceV2.sqrtFunction.body=true ∧
    stmtWithin 4 32 RamanujanPV.QuotientCSourceV2.countFunction.body=true := by
  decide +kernel

/-- Both arrays are represented through actual checked heap reads. No count is
assumed at an unrepresented or out-of-range address. -/
def HeapRep (heap : Heap) (smallBase largeBase r : Nat) (T : Tables) : Prop :=
  smallBase  ≠  largeBase ∧
    (∀ v, 1   ≤   v → v   ≤   r → QuotientCMachine.read heap smallBase v=some (.u64 (T.small v))) ∧
    (∀ i, 1   ≤   i → i   ≤   r → QuotientCMachine.read heap largeBase i=some (.u64 (T.large i)))

lemma read_some_details {heap : Heap} {base i old : Nat}
    (hread : QuotientCMachine.read heap base i=some (.u64 old)) :
    ∃ block, heap base=some block ∧ base%8=0 ∧ i < block.extent ∧
      base+8*i+8   ≤   modulus ∧ block.words i=old ∧ old < modulus := by
  cases hb : heap base with
  | none => simp [QuotientCMachine.read,hb] at hread
  | some block =>
    have hcond : base%8=0 ∧ i < block.extent ∧ base+8*i+8   ≤   modulus ∧ block.words i < modulus := by
      by_contra bad
      simp [QuotientCMachine.read,hb,bad] at hread
    have heq : block.words i=old := by simpa [QuotientCMachine.read,hb,hcond] using hread
    exact ⟨block,rfl,hcond.1,hcond.2.1,hcond.2.2.1,heq,heq ▸ hcond.2.2.2⟩

/-- One actual checked uint64 heap store, including all disjoint-address and
other-index frame effects. -/
theorem write_from_read {heap : Heap} {base i old value : Nat}
    (hread : QuotientCMachine.read heap base i=some (.u64 old)) (hv : value < modulus) :
    ∃ after, write heap base i value=some after ∧
      QuotientCMachine.read after base i=some (.u64 value) ∧
      (∀ other j, other ≠ base → QuotientCMachine.read after other j=QuotientCMachine.read heap other j) ∧
      (∀ j, j ≠ i → QuotientCMachine.read after base j=QuotientCMachine.read heap base j) := by
  obtain ⟨block,hb,halign,hi,haddr,hvalue,hold⟩ := read_some_details hread
  let after : Heap := Function.update heap base
    (some {block with words:=Function.update block.words i value})
  refine ⟨after,write_of_block hb halign hi haddr hv,?_,?_,?_⟩
  · have h := read_of_block (heap:=after) (base:=base) (index:=i)
      (block:={block with words:=Function.update block.words i value})
      (by simp [after]) halign hi haddr (by simpa using hv)
    simpa using h
  · intro other j hother
    simp only [QuotientCMachine.read, after, Function.update_of_ne hother]
  · intro j hji
    simp [QuotientCMachine.read,after,hb,Function.update_of_ne hji]

/-- The machine store refines exactly the mathematical large-table update and
preserves real allocation ownership. -/
theorem heap_large_update {heap : Heap} {sb lb r i value : Nat} {T : Tables}
    (owned : Owned heap) (rep : HeapRep heap sb lb r T)
    (hi : 1   ≤   i) (hir : i   ≤   r) (hv : value < modulus) :
    ∃ after, write heap lb i value=some after ∧ Owned after ∧
      HeapRep after sb lb r {T with large:=Function.update T.large i value} := by
  obtain ⟨after,hw,hsame,hother,hindex⟩ := write_from_read (rep.2.2 i hi hir) hv
  refine ⟨after,hw,write_preserves_owned owned hw,rep.1,?_,?_⟩
  · intro v hv hvr
    rw [hother sb v rep.1]
    exact rep.2.1 v hv hvr
  · intro j hj hjr
    by_cases hji : j=i
    · subst j
      simpa using hsame
    · change QuotientCMachine.read after lb j=some (.u64 (Function.update T.large i value j))
      rw [hindex j hji,Function.update_of_ne hji]
      exact rep.2.2 j hj hjr

theorem heap_small_update {heap : Heap} {sb lb r i value : Nat} {T : Tables}
    (owned : Owned heap) (rep : HeapRep heap sb lb r T)
    (hi : 1   ≤   i) (hir : i   ≤   r) (hv : value < modulus) :
    ∃ after, write heap sb i value=some after ∧ Owned after ∧
      HeapRep after sb lb r {T with small:=Function.update T.small i value} := by
  obtain ⟨after,hw,hsame,hother,hindex⟩ := write_from_read (rep.2.1 i hi hir) hv
  refine ⟨after,hw,write_preserves_owned owned hw,rep.1,?_,?_⟩
  · intro j hj hjr
    by_cases hji : j=i
    · subst j
      simpa using hsame
    · change QuotientCMachine.read after sb j=some (.u64 (Function.update T.small i value j))
      rw [hindex j hji,Function.update_of_ne hji]
      exact rep.2.1 j hj hjr
  · intro j hj hjr
    rw [hother lb j (Ne.symm rep.1)]
    exact rep.2.2 j hj hjr

/-- One actual source assignment shared by the large and small iterations. -/
def arraySubStore (array indexName : String) : Expr :=
  bin "=" (index array (var indexName)) (bin "-" (index array (var indexName)) subBefore)

theorem actual_large_store : seqAt largeBody 5=some (.eval (arraySubStore "large" "i")) := rfl
theorem actual_small_store : seqAt smallBody 3=some (.eval (arraySubStore "small" "v")) := rfl

/-- Execution of the actual typed source assignment. Both subtractions are
proved exact before reducing the generic modular uint64 operations. -/
theorem array_sub_store_eval {call : Service} {s : State} {after : Heap}
    {array indexName : String} {base i old sub before : Nat}
    (ha : s.env array=some (.ptr base)) (hi : s.env indexName=some (.u64 i))
    (hs : s.env "sub"=some (.u64 sub)) (hb : s.env "before"=some (.u64 before))
    (hr : QuotientCMachine.read s.heap base i=some (.u64 old))
    (hsub : sub < modulus) (hold : old < modulus)
    (hbefore : before  ≤  sub) (hdiff : sub-before  ≤  old)
    (hw : write s.heap base i (old-(sub-before))=some after) :
    Eval call (arraySubStore array indexName) s {s with heap:=after} (.u64 (old-(sub-before))) := by
  have hnew : old-(sub-before) < modulus := (Nat.sub_le _ _).trans_lt hold
  have hd1 := binary_u64_sub hbefore hsub
  have hd2 := binary_u64_sub hdiff hold
  have hread7 : evalPure call s.heap s.env 7 (index array (var indexName)) =
      some (.u64 old) :=
    pure_index_of ((pure_var call s.heap s.env 5 array).trans ha)
      ((pure_var call s.heap s.env 5 indexName).trans hi) hr
  have hsub7 : evalPure call s.heap s.env 7 subBefore = some (.u64 (sub-before)) :=
    pure_binary_of ((pure_var call s.heap s.env 5 "sub").trans hs)
      ((pure_var call s.heap s.env 5 "before").trans hb) hd1
  have hrhs : evalPure call s.heap s.env 8
      (bin "-" (index array (var indexName)) subBefore)=some (.u64 (old-(sub-before))) :=
    pure_binary_of hread7 hsub7 hd2
  exact eval_index_store_of
    ((pure_var call s.heap s.env 7 array).trans ha)
    ((pure_var call s.heap s.env 7 indexName).trans hi) hrhs (uint64_of_u64 hnew) hw

/-- The source store carries its actual typed execution, heap ownership and
functional table refinement together. This is a source-statement result;
full iteration/function composition remains a separate obligation. -/
theorem large_store_refines {call : Service} {s : State} {sb lb r i sub before : Nat} {T : Tables}
    (owned : Owned s.heap) (rep : HeapRep s.heap sb lb r T)
    (hi1 : 1  ≤  i) (hir : i  ≤  r)
    (ha : s.env "large"=some (.ptr lb)) (hi : s.env "i"=some (.u64 i))
    (hs : s.env "sub"=some (.u64 sub)) (hb : s.env "before"=some (.u64 before))
    (hsub : sub < modulus) (hbefore : before  ≤  sub) (hdiff : sub-before  ≤  T.large i) :
    ∃ t, Run call (.eval (arraySubStore "large" "i")) s (.continuing t) ∧
      t.env=s.env ∧ Owned t.heap ∧
      HeapRep t.heap sb lb r {T with large:=Function.update T.large i (T.large i-(sub-before))} := by
  have hr := rep.2.2 i hi1 hir
  obtain ⟨block,hblock,halign,hindex,haddress,hvalue,hold⟩ := read_some_details hr
  have hnew : T.large i-(sub-before) < modulus := (Nat.sub_le _ _).trans_lt hold
  obtain ⟨after,hw,owned',rep'⟩ := heap_large_update owned rep hi1 hir hnew
  refine ⟨{s with heap:=after},?_,rfl,owned',rep'⟩
  apply LCMSourcePV.ASTLoops.StmtRun.evaluate
  exact array_sub_store_eval ha hi hs hb hr hsub hold hbefore hdiff hw

theorem small_store_refines {call : Service} {s : State} {sb lb r i sub before : Nat} {T : Tables}
    (owned : Owned s.heap) (rep : HeapRep s.heap sb lb r T)
    (hi1 : 1  ≤  i) (hir : i  ≤  r)
    (ha : s.env "small"=some (.ptr sb)) (hi : s.env "v"=some (.u64 i))
    (hs : s.env "sub"=some (.u64 sub)) (hb : s.env "before"=some (.u64 before))
    (hsub : sub < modulus) (hbefore : before  ≤  sub) (hdiff : sub-before  ≤  T.small i) :
    ∃ t, Run call (.eval (arraySubStore "small" "v")) s (.continuing t) ∧
      t.env=s.env ∧ Owned t.heap ∧
      HeapRep t.heap sb lb r {T with small:=Function.update T.small i (T.small i-(sub-before))} := by
  have hr := rep.2.1 i hi1 hir
  obtain ⟨block,hblock,halign,hindex,haddress,hvalue,hold⟩ := read_some_details hr
  have hnew : T.small i-(sub-before) < modulus := (Nat.sub_le _ _).trans_lt hold
  obtain ⟨after,hw,owned',rep'⟩ := heap_small_update owned rep hi1 hir hnew
  refine ⟨{s with heap:=after},?_,rfl,owned',rep'⟩
  apply LCMSourcePV.ASTLoops.StmtRun.evaluate
  exact array_sub_store_eval ha hi hs hb hr hsub hold hbefore hdiff hw

/-- Exact source small-loop body, including its fresh `sub` local, both
underflow failure tests, the checked store, decrement, and lexical exit. -/
theorem small_body_exec {call : Service} {s : State} {sb lb r p v before : Nat} {T : Tables}
    (owned : Owned s.heap) (rep : HeapRep s.heap sb lb r T)
    (hv1 : 1 ≤ v) (hvr : v ≤ r) (hp : 0 < p) (hvw : v < modulus)
    (hq1 : 1 ≤ v/p) (hqr : v/p ≤ r)
    (hsmall : s.env "small"=some (.ptr sb))
    (hvalue : s.env "v"=some (.u64 v)) (hprime : s.env "p"=some (.u64 p))
    (hbeforeEnv : s.env "before"=some (.u64 before)) (hfresh : s.env "sub"=none)
    (hbefore : before ≤ T.small (v/p))
    (hdiff : T.small (v/p)-before ≤ T.small v) :
    ∃ t, Run call smallBody s (.continuing t) ∧
      t.env=bind s.env "v" (.u64 (v-1)) ∧ Owned t.heap ∧
      HeapRep t.heap sb lb r (smallStep p before v T) := by
  let sub := T.small (v/p)
  obtain ⟨block,hblock,halign,hindex,haddress,hword,hsub⟩ :=
    read_some_details (rep.2.1 (v/p) hq1 hqr)
  have hsubw : sub < modulus := hsub
  let t1 : State := {s with env:=bind s.env "sub" (.u64 sub)}
  have hdecl : Declare call [⟨"uint64_t","sub",some
      (index "small" (bin "/" (var "v") (var "p")))⟩] s t1 :=
    declare_singleton_of hfresh
      (pure_index_of ((pure_var call s.heap s.env 6 "small").trans hsmall)
        (pure_binary_of ((pure_var call s.heap s.env 5 "v").trans hvalue)
          ((pure_var call s.heap s.env 5 "p").trans hprime) (binary_u64_div hp hvw))
        (rep.2.1 (v/p) hq1 hqr)) (uint64_of_u64 hsubw)
  have hs1 : t1.env "sub"=some (.u64 sub) := by simp [t1]
  have hb1 : t1.env "before"=some (.u64 before) := by simp [t1,hbeforeEnv]
  have hvLook : t1.env "v"=some (.u64 v) := by simp [t1,hvalue]
  have ha1 : t1.env "small"=some (.ptr sb) := by simp [t1,hsmall]
  have hg1 : Eval call (bin "<" (var "sub") (var "before")) t1 t1 (.i32 0) := by
    exact (eval_lt_of ((pure_var call t1.heap t1.env 6 "sub").trans hs1)
      ((pure_var call t1.heap t1.env 6 "before").trans hb1)).trans
        (by rw [if_neg (by omega : ¬sub<before)])
  have hread7 : evalPure call t1.heap t1.env 7 (index "small" (var "v")) =
      some (.u64 (T.small v)) :=
    pure_index_of ((pure_var call t1.heap t1.env 5 "small").trans ha1)
      ((pure_var call t1.heap t1.env 5 "v").trans hvLook) (rep.2.1 v hv1 hvr)
  have hdiff7 : evalPure call t1.heap t1.env 7 subBefore=some (.u64 (sub-before)) :=
    pure_binary_of ((pure_var call t1.heap t1.env 5 "sub").trans hs1)
      ((pure_var call t1.heap t1.env 5 "before").trans hb1) (binary_u64_sub hbefore hsubw)
  have hg2 : Eval call (bin "<" (index "small" (var "v")) subBefore) t1 t1 (.i32 0) := by
    exact (eval_lt_of hread7 hdiff7).trans (by rw [if_neg (by omega : ¬T.small v<sub-before)])
  obtain ⟨t2,hstore,henv2,hown2,hrep2⟩ :=
    small_store_refines (s:=t1) owned rep hv1 hvr ha1 hvLook hs1 hb1 hsubw hbefore hdiff
  let t3 : State := {t2 with env:=bind t2.env "v" (.u64 (v-1))}
  have hd : Eval call (.unary "--" (var "v")) t2 t3 (.u64 (v-1)) := by
    have hval : t2.env "v"=some (.u64 v) := henv2 ▸ hvLook
    have hid : v+modulus-1=(v-1)+modulus := by omega
    have hvw' : v-1 < modulus := (Nat.sub_le _ _).trans_lt hvw
    simp [Eval,eval_decrement,var,hval,hid,Nat.mod_eq_of_lt hvw',t3]
  let t := closeScope s t3
  have henvt : t.env=bind s.env "v" (.u64 (v-1)) := by
    funext name
    by_cases hn : name="v"
    · subst name
      simp [t,t3,closeScope,henv2,hvalue]
    · by_cases hs : name="sub"
      · subst name
        simp [t,closeScope,hfresh,QuotientCMachine.bind,hn]
      · simp only [t,t3,closeScope,henv2,t1]
        simp only [QuotientCMachine.bind,Function.update_of_ne hn,Function.update_of_ne hs]
        cases h : s.env name <;> simp [h]
  refine ⟨t,?_,henvt,hown2,hrep2⟩
  apply LCMSourcePV.ASTLoops.StmtRun.sequence (inner:=.continuing t3)
  · apply LCMSourcePV.ASTLoops.SeqRun.next (LCMSourcePV.ASTLoops.StmtRun.declare hdecl)
    apply LCMSourcePV.ASTLoops.SeqRun.next
      (LCMSourcePV.ASTLoops.StmtRun.branch hg1 (by
        simpa [truth,Value.bits] using LCMSourcePV.ASTLoops.StmtRun.skip (Eval:=Eval call)
          (Declare:=Declare call) (truth:=truth) (Scope:=Scope) t1))
    apply LCMSourcePV.ASTLoops.SeqRun.next
      (LCMSourcePV.ASTLoops.StmtRun.branch hg2 (by
        simpa [truth,Value.bits] using LCMSourcePV.ASTLoops.StmtRun.skip (Eval:=Eval call)
          (Declare:=Declare call) (truth:=truth) (Scope:=Scope) t1))
    exact LCMSourcePV.ASTLoops.SeqRun.next hstore
      (LCMSourcePV.ASTLoops.SeqRun.next (LCMSourcePV.ASTLoops.StmtRun.evaluate hd)
        (LCMSourcePV.ASTLoops.SeqRun.nil t3))
  · rfl

#print axioms small_body_exec
#print axioms array_sub_store_eval
#print axioms large_store_refines
#print axioms small_store_refines
#print axioms actual_large_body
#print axioms actual_small_body
#print axioms heap_large_update
#print axioms heap_small_update
end RamanujanPV.QuotientCExecute
