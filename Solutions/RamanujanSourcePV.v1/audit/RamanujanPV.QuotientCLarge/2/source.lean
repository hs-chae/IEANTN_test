/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import RamanujanPV.QuotientCExecute

/-! Actual ascending quotient-table source execution. This component does not
claim that a concrete full native execution has been kernel accepted. -/
namespace RamanujanPV.QuotientCLarge
open LCMSourcePV.Witness.C
open QuotientCMachine QuotientTables QuotientCExecute
set_option autoImplicit false
set_option maxHeartbeats 2000000

private def var (name : String) : Expr := .var name
private def bin (op : String) (a b : Expr) : Expr := .binary op a b
private def index (name : String) (i : Expr) : Expr := .index (.var name) i
private def subBefore : Expr := bin "-" (var "sub") (var "before")

lemma close_two_fresh {s t : State} {a b : String} {va vb : Value}
    (ha : s.env a=none) (hb : s.env b=none)
    (henv : t.env=bind (bind s.env a va) b vb) : (closeScope s t).env=s.env := by
  funext name
  simp only [closeScope,henv]
  by_cases hnb : name=b
  · subst name
    simp [hb]
  · by_cases hna : name=a
    · subst name
      simp [ha]
    · simp only [QuotientCMachine.bind,Function.update_of_ne hnb,Function.update_of_ne hna]
      cases h : s.env name <;> simp [h]

/-- The actual six source statements of one ascending large-table iteration.
The represented table values determine every read; numeric guards are explicit
premises here and are discharged from the survivor invariant in the loop theorem. -/
theorem large_body_exec {call : Service} {s : State} {sb lb N r p i before : Nat} {T : Tables}
    (owned : Owned s.heap) (rep : HeapRep s.heap sb lb r T)
    (hi1 : 1 ≤ i) (hir : i ≤ r) (hip0 : 0 < i*p)
    (hipw : i*p < modulus) (hNw : N < modulus)
    (hreadIndex : if i*p ≤ r then 1 ≤ i*p else 1 ≤ N/(i*p) ∧ N/(i*p) ≤ r)
    (hn : s.env "n"=some (.u64 N)) (hr : s.env "r"=some (.u64 r))
    (hp : s.env "p"=some (.u64 p)) (hi : s.env "i"=some (.u64 i))
    (hsmall : s.env "small"=some (.ptr sb)) (hlarge : s.env "large"=some (.ptr lb))
    (hb : s.env "before"=some (.u64 before))
    (hfreshIp : s.env "ip"=none) (hfreshSub : s.env "sub"=none)
    (hbefore : before ≤ largeRead N r p i T)
    (hdiff : largeRead N r p i T-before ≤ T.large i) :
    ∃ t, Run call largeBody s (.continuing t) ∧ t.env=s.env ∧
      Owned t.heap ∧ HeapRep t.heap sb lb r (largeStep N r p before i T) := by
  let sub := largeRead N r p i T
  let t1 : State := {s with env:=bind s.env "ip" (.u64 (i*p))}
  let t2 : State := {t1 with env:=bind t1.env "sub" (.u64 0)}
  let t3 : State := {t2 with env:=bind t2.env "sub" (.u64 sub)}
  have hdeclIp : Declare call [⟨"uint64_t","ip",some (bin "*" (var "i") (var "p"))⟩] s t1 :=
    declare_singleton_of hfreshIp
      (pure_binary_of ((pure_var call s.heap s.env 6 "i").trans hi)
        ((pure_var call s.heap s.env 6 "p").trans hp) (binary_u64_mul hipw))
      (uint64_of_u64 hipw)
  have hsubNone : t1.env "sub"=none := by simp [t1,hfreshSub]
  have hdeclSub : Declare call [⟨"uint64_t","sub",some (.nat 0)⟩] t1 t2 :=
    declare_singleton_of (raw:=.i32 0) hsubNone
      ((pure_literal call t1.heap t1.env 7 0).trans (by norm_num [literal]))
      (by norm_num [uint64,Value.scalar,modulus])
  have hip2 : t2.env "ip"=some (.u64 (i*p)) := by simp [t2,t1]
  have hr2 : t2.env "r"=some (.u64 r) := by simp [t2,t1,hr]
  have hn2 : t2.env "n"=some (.u64 N) := by simp [t2,t1,hn]
  have hsmall2 : t2.env "small"=some (.ptr sb) := by simp [t2,t1,hsmall]
  have hlarge2 : t2.env "large"=some (.ptr lb) := by simp [t2,t1,hlarge]
  have hzero2 : t2.env "sub"=some (.u64 0) := by simp [t2]
  have test : Eval call (bin "<=" (var "ip") (var "r")) t2 t2
      (.i32 (if i*p≤r then 1 else 0)) :=
    eval_le_of ((pure_var call t2.heap t2.env 6 "ip").trans hip2)
      ((pure_var call t2.heap t2.env 6 "r").trans hr2)
  have readBranch : Run call
      (.branch (bin "<=" (var "ip") (var "r"))
        (.eval (bin "=" (var "sub") (index "large" (var "ip"))))
        (.eval (bin "=" (var "sub") (index "small" (bin "/" (var "n") (var "ip"))))))
      t2 (.continuing t3) := by
    apply LCMSourcePV.ASTLoops.StmtRun.branch test
    by_cases hbig : i*p≤r
    · have hj : 1 ≤ i*p := by simpa [hbig] using hreadIndex
      have hread := rep.2.2 (i*p) hj hbig
      obtain ⟨B,hB,hA,hI,hAddr,hValue,hW⟩ := read_some_details hread
      have subeq : sub=T.large (i*p) := by simp [sub,largeRead,hbig]
      have he : Eval call (bin "=" (var "sub") (index "large" (var "ip"))) t2 t3 (.u64 sub) :=
        eval_variable_assign_of hzero2
          (pure_index_of ((pure_var call t2.heap t2.env 6 "large").trans hlarge2)
            ((pure_var call t2.heap t2.env 6 "ip").trans hip2) (subeq ▸ hread))
          (uint64_of_u64 (subeq ▸ hW))
      simpa [hbig,truth,Value.bits] using LCMSourcePV.ASTLoops.StmtRun.evaluate he
    · have hj : 1 ≤ N/(i*p) ∧ N/(i*p)≤r := by simpa [hbig] using hreadIndex
      have hread := rep.2.1 (N/(i*p)) hj.1 hj.2
      obtain ⟨B,hB,hA,hI,hAddr,hValue,hW⟩ := read_some_details hread
      have subeq : sub=T.small (N/(i*p)) := by simp [sub,largeRead,hbig]
      have he : Eval call (bin "=" (var "sub") (index "small" (bin "/" (var "n") (var "ip"))))
          t2 t3 (.u64 sub) :=
        eval_variable_assign_of hzero2
          (pure_index_of ((pure_var call t2.heap t2.env 6 "small").trans hsmall2)
            (pure_binary_of ((pure_var call t2.heap t2.env 5 "n").trans hn2)
              ((pure_var call t2.heap t2.env 5 "ip").trans hip2) (binary_u64_div hip0 hNw))
            (subeq ▸ hread)) (uint64_of_u64 (subeq ▸ hW))
      simpa [hbig,truth,Value.bits] using LCMSourcePV.ASTLoops.StmtRun.evaluate he
  have hs3 : t3.env "sub"=some (.u64 sub) := by simp [t3]
  have hb3 : t3.env "before"=some (.u64 before) := by simp [t3,t2,t1,hb]
  have hi3 : t3.env "i"=some (.u64 i) := by simp [t3,t2,t1,hi]
  have hl3 : t3.env "large"=some (.ptr lb) := by simp [t3,t2,t1,hlarge]
  have hsubw : sub < modulus := by
    by_cases hbig : i*p≤r
    · have hj : 1 ≤ i*p := by simpa [hbig] using hreadIndex
      obtain ⟨B,hB,hA,hI,hAddr,hValue,hW⟩ := read_some_details (rep.2.2 (i*p) hj hbig)
      simpa [sub,largeRead,hbig] using hW
    · have hj : 1 ≤ N/(i*p) ∧ N/(i*p)≤r := by simpa [hbig] using hreadIndex
      obtain ⟨B,hB,hA,hI,hAddr,hValue,hW⟩ := read_some_details (rep.2.1 (N/(i*p)) hj.1 hj.2)
      simpa [sub,largeRead,hbig] using hW
  have guard1 : Eval call (bin "<" (var "sub") (var "before")) t3 t3 (.i32 0) :=
    (eval_lt_of ((pure_var call t3.heap t3.env 6 "sub").trans hs3)
      ((pure_var call t3.heap t3.env 6 "before").trans hb3)).trans
        (by rw [if_neg (by omega : ¬sub<before)])
  have guard2 : Eval call (bin "<" (index "large" (var "i")) subBefore) t3 t3 (.i32 0) :=
    (eval_lt_of
      (pure_index_of ((pure_var call t3.heap t3.env 5 "large").trans hl3)
        ((pure_var call t3.heap t3.env 5 "i").trans hi3) (rep.2.2 i hi1 hir))
      (pure_binary_of ((pure_var call t3.heap t3.env 5 "sub").trans hs3)
        ((pure_var call t3.heap t3.env 5 "before").trans hb3) (binary_u64_sub hbefore hsubw))).trans
        (by rw [if_neg (by omega : ¬T.large i<sub-before)])
  obtain ⟨t4,hstore,henv4,hown4,hrep4⟩ :=
    large_store_refines (s:=t3) owned rep hi1 hir hl3 hi3 hs3 hb3 hsubw hbefore hdiff
  let t := closeScope s t4
  have henv4' : t4.env=bind (bind s.env "ip" (.u64 (i*p))) "sub" (.u64 sub) := by
    rw [henv4]
    simp [t3,t2,t1,QuotientCMachine.bind,Function.update_idem]
  refine ⟨t,?_,close_two_fresh hfreshIp hfreshSub henv4',hown4,hrep4⟩
  apply LCMSourcePV.ASTLoops.StmtRun.sequence (inner:=.continuing t4)
  · apply LCMSourcePV.ASTLoops.SeqRun.next (LCMSourcePV.ASTLoops.StmtRun.declare hdeclIp)
    apply LCMSourcePV.ASTLoops.SeqRun.next (LCMSourcePV.ASTLoops.StmtRun.declare hdeclSub)
    apply LCMSourcePV.ASTLoops.SeqRun.next readBranch
    apply LCMSourcePV.ASTLoops.SeqRun.next (LCMSourcePV.ASTLoops.StmtRun.branch guard1 (by
      simpa [truth,Value.bits] using LCMSourcePV.ASTLoops.StmtRun.skip (Eval:=Eval call)
        (Declare:=Declare call) (truth:=truth) (Scope:=Scope) t3))
    apply LCMSourcePV.ASTLoops.SeqRun.next (LCMSourcePV.ASTLoops.StmtRun.branch guard2 (by
      simpa [truth,Value.bits] using LCMSourcePV.ASTLoops.StmtRun.skip (Eval:=Eval call)
        (Declare:=Declare call) (truth:=truth) (Scope:=Scope) t3))
    exact LCMSourcePV.ASTLoops.SeqRun.next hstore (LCMSourcePV.ASTLoops.SeqRun.nil t4)
  · rfl

#print axioms large_body_exec
end RamanujanPV.QuotientCLarge
