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

/-- The actual source loop tree, including the fresh loop index. -/
def largeGuard : Expr := bin "<=" (var "i") (var "stop")
def largeIncrement : Expr := .unary "++" (var "i")
def largeFor : Stmt := .forLoop
  (.declare [⟨"uint64_t","i",some (.nat 1)⟩]) (some largeGuard) largeIncrement largeBody

def actualLargeFor : Option Stmt := do
  let outer ← match QuotientCSourceV2.countFunction.body with
    | .sequence xs => xs[5]? | _ => none
  let branch ← match outer with | .forLoop _ _ _ body => some body | _ => none
  let active ← match branch with | .branch _ _ no => some no | _ => none
  match active with | .sequence xs => xs[3]? | _ => none

theorem actual_large_for : actualLargeFor=some largeFor := rfl

structure LoopEnv (sb lb N r p before stop : Nat) (env : Env) : Prop where
  n : env "n"=some (.u64 N)
  rValue : env "r"=some (.u64 r)
  pValue : env "p"=some (.u64 p)
  beforeValue : env "before"=some (.u64 before)
  stopValue : env "stop"=some (.u64 stop)
  small : env "small"=some (.ptr sb)
  large : env "large"=some (.ptr lb)
  ipFresh : env "ip"=none
  subFresh : env "sub"=none

lemma LoopEnv.bind_i {sb lb N r p before stop : Nat} {env : Env}
    (h : LoopEnv sb lb N r p before stop env) (value : Value) :
    LoopEnv sb lb N r p before stop (bind env "i" value) := by
  exact {
    n := by simpa using h.n
    rValue := by simpa using h.rValue
    pValue := by simpa using h.pValue
    beforeValue := by simpa using h.beforeValue
    stopValue := by simpa using h.stopValue
    small := by simpa using h.small
    large := by simpa using h.large
    ipFresh := by simpa using h.ipFresh
    subFresh := by simpa using h.subFresh }

/-- Complete source for-loop suffix, with no assumed successful failure tests.
All such tests follow from the current survivor-cardinality invariant. -/
theorem large_for_remaining {call : Service} {sb lb N r p before : Nat} {T : Tables}
    (hN : N  ≤  2000000000000) (hr : r=N.sqrt) (hp : Nat.Prime p) (hpr : p ≤ r)
    (hbefore : before=QuotientSieve.total p (p-1)) (hinit : Invariant N r p T) :
    ∀ fuel k, k ≤ largeStop N r p → largeStop N r p < k+fuel →
      ∀ s : State, LoopEnv sb lb N r p before (largeStop N r p) s.env →
      s.env "i"=some (.u64 (k+1)) → Owned s.heap →
      HeapRep s.heap sb lb r (largeLoop N r p before k T) →
      ∃ t, ForRun call (some largeGuard) largeIncrement largeBody s (.continuing t) ∧
        t.env=bind s.env "i" (.u64 (largeStop N r p+1)) ∧ Owned t.heap ∧
        HeapRep t.heap sb lb r (largeLoop N r p before (largeStop N r p) T) := by
  have hroot : N < (r+1)*(r+1) := by simpa [hr,Nat.succ_eq_add_one] using Nat.lt_succ_sqrt N
  have hNw : N < modulus := by norm_num [modulus]; omega
  have hrN : r ≤ N := by simpa [hr] using Nat.sqrt_le_self N
  intro fuel
  induction fuel with
  | zero => intro k hk hf; omega
  | succ fuel ih =>
    intro k hk hf s env hi owned rep
    by_cases keep : k < largeStop N r p
    · have histop : k+1 ≤ min r (N/(p*p)) := keep
      have hir : k+1 ≤ r := histop.trans (Nat.min_le_left _ _)
      have hisquare : k+1 ≤ N/(p*p) := histop.trans (Nat.min_le_right _ _)
      have bounds := QuotientWordBounds.word_index_bounds_sqrt hN hr hp.two_le hpr
        (by omega : 1 ≤ k+1) histop
      have stage := largeLoop_stage hp hroot hbefore hinit k hk
      have readCorrect := large_read_correct hp (by omega : 1 ≤ k+1) hir hisquare hroot stage
      have oldCorrect : (largeLoop N r p before k T).large (k+1)=QuotientSieve.total p (N/(k+1)) := by
        rw [stage.2 (k+1) (by omega) hir,if_neg (by omega)]
      have guards := QuotientWordBounds.large_cell_subtraction_guards hp (by omega : 1 ≤ k+1) histop
      have guard1 : before ≤ largeRead N r p (k+1) (largeLoop N r p before k T) := by
        rw [readCorrect,hbefore]
        exact guards.1
      have guard2 : largeRead N r p (k+1) (largeLoop N r p before k T)-before ≤ 
          (largeLoop N r p before k T).large (k+1) := by
        rw [readCorrect,hbefore,oldCorrect]
        exact guards.2
      have readIndex : if (k+1)*p ≤ r then 1 ≤ (k+1)*p else
          1 ≤ N/((k+1)*p) ∧ N/((k+1)*p) ≤ r := by
        split_ifs with hb
        · have pos := Nat.mul_pos (by omega : 0 < k+1) hp.pos; omega
        · exact bounds.2.2.2.2.2.1 (by omega)
      obtain ⟨b,iteration,envb,ownedb,repb⟩ := large_body_exec owned rep (by omega) hir
        (Nat.mul_pos (by omega) hp.pos) bounds.2.1 hNw readIndex env.n env.rValue env.pValue hi
        env.small env.large env.beforeValue env.ipFresh env.subFresh guard1 guard2
      let c : State := {b with env:=bind b.env "i" (.u64 (k+2))}
      have incWord : k+2 < modulus := by have h : k+1 ≤ N := hir.trans hrN; norm_num [modulus]; omega
      have increment : Eval call largeIncrement b c (.u64 (k+2)) := by
        simp [Eval,largeIncrement,var,eval_increment,envb,hi,Nat.mod_eq_of_lt incWord,c]
      have envc : LoopEnv sb lb N r p before (largeStop N r p) c.env := by
        change LoopEnv sb lb N r p before (largeStop N r p) (bind b.env "i" (.u64 (k+2)))
        rw [envb]
        exact env.bind_i _
      have ic : c.env "i"=some (.u64 ((k+1)+1)) := by simp [c,Nat.add_assoc]
      obtain ⟨t,rest,envt,ownedt,rept⟩ := ih (k+1) (by omega) (by omega) c envc ic ownedb repb
      refine ⟨t,?_,?_,ownedt,rept⟩
      · have test : Eval call largeGuard s s (.i32 1) :=
          (eval_le_of ((pure_var call s.heap s.env 6 "i").trans hi)
            ((pure_var call s.heap s.env 6 "stop").trans env.stopValue)).trans
            (by rw [if_pos (by omega : k+1 ≤ largeStop N r p)])
        exact LCMSourcePV.ASTLoops.ForRun.next
          (by simpa [truth,Value.bits] using LCMSourcePV.ASTLoops.GuardRun.present test)
          iteration increment rest
      · rw [envt]
        simp [c,envb,QuotientCMachine.bind,Function.update_idem]
    · have keq : k=largeStop N r p := by omega
      refine ⟨s,?_,?_,owned,?_⟩
      · have test : Eval call largeGuard s s (.i32 0) :=
          (eval_le_of ((pure_var call s.heap s.env 6 "i").trans hi)
            ((pure_var call s.heap s.env 6 "stop").trans env.stopValue)).trans
            (by rw [if_neg (by omega : ¬k+1 ≤ largeStop N r p)])
        exact LCMSourcePV.ASTLoops.ForRun.done
          (by simpa [truth,Value.bits] using LCMSourcePV.ASTLoops.GuardRun.present test)
      · funext name
        by_cases hn : name="i"
        · subst name
          simpa [keq] using hi
        · simp [QuotientCMachine.bind,hn]
      · simpa [keq] using rep

/-- Actual fresh-i source for-loop, with all numerical, table and underflow
obligations discharged from the prime-survivor invariant. -/
theorem large_for_exec {call : Service} {s : State} {sb lb N r p before : Nat} {T : Tables}
    (hN : N ≤ 2000000000000) (hr : r=N.sqrt) (hp : Nat.Prime p) (hpr : p ≤ r)
    (hbefore : before=QuotientSieve.total p (p-1)) (hinit : Invariant N r p T)
    (owned : Owned s.heap) (rep : HeapRep s.heap sb lb r T)
    (env : LoopEnv sb lb N r p before (largeStop N r p) s.env) (freshI : s.env "i"=none) :
    ∃ t, Run call largeFor s (.continuing t) ∧ t.env=s.env ∧ Owned t.heap ∧
      HeapRep t.heap sb lb r (largeLoop N r p before (largeStop N r p) T) := by
  let started : State := {s with env:=bind s.env "i" (.u64 1)}
  have declaration : Declare call [⟨"uint64_t","i",some (.nat 1)⟩] s started :=
    declare_singleton_of (raw:=.i32 1) freshI
      ((pure_literal call s.heap s.env 7 1).trans (by norm_num [literal]))
      (by norm_num [uint64,Value.scalar,modulus])
  have envStarted : LoopEnv sb lb N r p before (largeStop N r p) started.env := env.bind_i _
  obtain ⟨inner,loop,envInner,ownInner,repInner⟩ := large_for_remaining hN hr hp hpr hbefore hinit
    (largeStop N r p+1) 0 (by omega) (by omega) started envStarted (by simp [started]) owned rep
  let t := closeScope s inner
  refine ⟨t,?_,close_two_fresh freshI freshI envInner,ownInner,repInner⟩
  exact LCMSourcePV.ASTLoops.StmtRun.forLoop
    (LCMSourcePV.ASTLoops.StmtRun.declare declaration) loop rfl

#print axioms large_for_remaining
#print axioms large_for_exec
#print axioms large_body_exec
end RamanujanPV.QuotientCLarge
