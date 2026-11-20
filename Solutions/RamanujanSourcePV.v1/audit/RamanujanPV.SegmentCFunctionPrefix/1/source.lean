/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import RamanujanPV.SegmentCInit
import RamanujanPV.SegmentCDivisors

/-! Actual source prefix of the segmented checker. Claims are arbitrary input
words; only their memory representation, never their mathematical correctness,
is supplied. The source computes every prime/composite flag itself. -/
namespace RamanujanPV.SegmentCFunctionPrefix
open LCMSourcePV.Witness.C LCMSourcePV.ASTLoops QuotientCMachine
open SegmentMemory SegmentCheckerMath
set_option autoImplicit false
set_option maxHeartbeats 2000000

def input (lo hi capacity claims flags : Nat) (heap : Heap) : State :=
  ⟨bind (bind (bind (bind (bind emptyEnv "lo" (.u64 lo)) "hi" (.u64 hi))
    "capacity" (.u64 capacity)) "claims" (.ptr claims)) "flags" (.ptr flags),heap⟩

def lowerGuard : Stmt := .branch (.binary "<" (.var "lo") (.nat 2))
  (.returnStmt (.nat 0)) .skip
def orderGuard : Stmt := .branch (.binary "<" (.var "hi") (.var "lo"))
  (.returnStmt (.nat 0)) .skip
def upperGuard : Stmt := .branch (.binary ">" (.var "hi") (.nat 2000000000000))
  (.returnStmt (.nat 0)) .skip
def lengthExpr : Expr := .binary "+" (.binary "-" (.var "hi") (.var "lo")) (.nat 1)
def lengthDeclaration : Stmt := .declare [⟨"uint64_t","length",some lengthExpr⟩]
def capacityGuard : Stmt := .branch (.binary "<" (.var "capacity") (.var "length"))
  (.returnStmt (.nat 0)) .skip
def prefixStatements : List Stmt := [lowerGuard,orderGuard,upperGuard,lengthDeclaration,
  capacityGuard,SegmentCInit.initFor,SegmentCDivisors.divisorFor]

theorem actual_prefix : (match SegmentCheckerSource.checkerFunction.body with
    | .sequence body => body.take 7 | _ => []) = prefixStatements := rfl

structure Inputs (lo hi capacity cb fb : Nat) (env : Env) : Prop where
  loValue : env "lo"=some (.u64 lo)
  hiValue : env "hi"=some (.u64 hi)
  capacityValue : env "capacity"=some (.u64 capacity)
  claimsValue : env "claims"=some (.ptr cb)
  flagsValue : env "flags"=some (.ptr fb)
  lengthFresh : env "length"=none
  countFresh : env "count"=none
  iFresh : env "i"=none
  dFresh : env "d"=none
  firstFresh : env "first"=none
  mFresh : env "m"=none

theorem input_env (lo hi capacity cb fb : Nat) (heap : Heap) :
    Inputs lo hi capacity cb fb (input lo hi capacity cb fb heap).env := by
  constructor <;> simp [input,emptyEnv]

lemma length_pure {call : Service} {s : State} {lo hi : Nat}
    (hlo : s.env "lo"=some (.u64 lo)) (hhi : s.env "hi"=some (.u64 hi))
    (horder : lo≤hi) (hword : hi-lo+1<modulus) :
    evalPure call s.heap s.env 8 lengthExpr=some (.u64 (hi-lo+1)) := by
  apply pure_binary_of (raw:=.u64 (hi-lo)) (vb:=.i32 1)
    (pure_binary_of ((pure_var call s.heap s.env 5 "hi").trans hhi)
      ((pure_var call s.heap s.env 5 "lo").trans hlo) (binary_u64_sub horder))
    ((pure_literal call s.heap s.env 6 1).trans (by norm_num [literal]))
  simp [binary,Value.scalar,Nat.mod_eq_of_lt hword]

/-- Exact source guard, allocation initialization and complete divisor prefix.
The pre-existing claims buffer is preserved word for word by disjointness. -/
theorem prefix_exec {call : Service} {s : State} {lo hi capacity cb fb : Nat}
    {claims : Nat→Nat}
    (hlo : 2≤lo) (horder : lo≤hi) (hhi : hi≤2000000000000)
    (hcapacity : hi-lo+1≤capacity) (disjoint : cb≠fb)
    (owned : Owned s.heap) (buffer : SegmentCInit.Buffer s.heap fb (hi-lo+1))
    (claimRep : FlagsRep s.heap cb (hi-lo+1) claims)
    (env : Inputs lo hi capacity cb fb s.env) :
    ∃ t, SeqRun call prefixStatements s (.continuing t) ∧
      t.env=bind s.env "length" (.u64 (hi-lo+1)) ∧ Owned t.heap ∧
      FlagsRep t.heap fb (hi-lo+1) (finalFlags lo hi) ∧
      FlagsRep t.heap cb (hi-lo+1) claims := by
  have hiWord : hi<modulus := by norm_num [modulus]; omega
  have lenWord : hi-lo+1<modulus := by norm_num [modulus]; omega
  have lowerEval : Eval call (.binary "<" (.var "lo") (.nat 2)) s s (.i32 0) := by
    apply eval_pure_lt
    exact pure_binary_of (vb:=.i32 2)
      ((pure_var call s.heap s.env 6 "lo").trans env.loValue)
      ((pure_literal call s.heap s.env 6 2).trans (by norm_num [literal]))
      (by simp [binary,Value.scalar]; omega)
  have orderEval : Eval call (.binary "<" (.var "hi") (.var "lo")) s s (.i32 0) := by
    exact (eval_lt_of ((pure_var call s.heap s.env 6 "hi").trans env.hiValue)
      ((pure_var call s.heap s.env 6 "lo").trans env.loValue)).trans
      (by rw [if_neg (by omega : ¬hi<lo)])
  have upperEval : Eval call (.binary ">" (.var "hi") (.nat 2000000000000)) s s (.i32 0) := by
    apply eval_pure_gt
    exact pure_binary_of
      ((pure_var call s.heap s.env 6 "hi").trans env.hiValue)
      ((pure_literal call s.heap s.env 6 2000000000000).trans literal_two_trillion)
      (by simp [binary,Value.scalar,show ¬2000000000000<hi by omega])
  have lowerRun : Run call lowerGuard s (.continuing s) := by
    apply StmtRun.branch lowerEval
    simpa [truth,Value.bits] using StmtRun.skip (Eval:=Eval call)
      (Declare:=Declare call) (truth:=truth) (Scope:=Scope) s
  have orderRun : Run call orderGuard s (.continuing s) := by
    apply StmtRun.branch orderEval
    simpa [truth,Value.bits] using StmtRun.skip (Eval:=Eval call)
      (Declare:=Declare call) (truth:=truth) (Scope:=Scope) s
  have upperRun : Run call upperGuard s (.continuing s) := by
    apply StmtRun.branch upperEval
    simpa [truth,Value.bits] using StmtRun.skip (Eval:=Eval call)
      (Declare:=Declare call) (truth:=truth) (Scope:=Scope) s
  let started : State := {s with env:=bind s.env "length" (.u64 (hi-lo+1))}
  have declaration : Declare call [⟨"uint64_t","length",some lengthExpr⟩] s started :=
    declare_singleton_of env.lengthFresh (length_pure env.loValue env.hiValue horder lenWord)
      (uint64_of_u64 lenWord)
  have capEval : Eval call (.binary "<" (.var "capacity") (.var "length"))
      started started (.i32 0) := by
    exact (eval_lt_of
      ((pure_var call started.heap started.env 6 "capacity").trans
        (by simpa [started] using env.capacityValue))
      ((pure_var call started.heap started.env 6 "length").trans (by simp [started]))).trans
      (by rw [if_neg (by omega : ¬capacity<hi-lo+1)])
  have capRun : Run call capacityGuard started (.continuing started) := by
    apply StmtRun.branch capEval
    simpa [truth,Value.bits] using StmtRun.skip (Eval:=Eval call)
      (Declare:=Declare call) (truth:=truth) (Scope:=Scope) started
  obtain ⟨initialized,hinit,heInit,ownedInit,bufferInit,onesInit,shapeInit,frameInit⟩ :=
    SegmentCInit.initialization_loop (s:=started) (call:=call) owned buffer
      (by simpa [started] using env.flagsValue) (by simp [started])
      (by simpa [started] using env.iFresh) lenWord
  have ones : FlagsRep initialized.heap fb (hi-lo+1) (fun _=>1) := onesInit
  obtain ⟨last,hdiv,heDiv,ownedDiv,repDiv,frameDiv⟩ := SegmentCDivisors.divisor_for_exec
    (s:=initialized) (call:=call) hlo horder hhi ownedInit ones
    (by simpa [heInit,started] using env.loValue)
    (by simpa [heInit,started] using env.hiValue)
    (by simpa [heInit,started] using env.flagsValue)
    (by simpa [heInit,started] using env.dFresh)
    (by simpa [heInit,started] using env.firstFresh)
    (by simpa [heInit,started] using env.mFresh)
  refine ⟨last,?_,heDiv.trans heInit,ownedDiv,repDiv,?_⟩
  · exact SeqRun.next lowerRun (SeqRun.next orderRun (SeqRun.next upperRun
      (SeqRun.next (StmtRun.declare declaration) (SeqRun.next capRun
        (SeqRun.next hinit (SeqRun.next hdiv (SeqRun.nil last)))))))
  · intro i hiIndex
    rw [frameDiv cb i disjoint]
    change QuotientCMachine.read initialized.heap cb i=_
    rw [show initialized.heap cb=s.heap cb from frameInit cb disjoint]
    exact claimRep i hiIndex

#print axioms actual_prefix
#print axioms prefix_exec
end RamanujanPV.SegmentCFunctionPrefix
