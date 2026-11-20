/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import RamanujanPV.SegmentCFunctionPrefix
import RamanujanPV.SegmentCClaims
import RamanujanPV.SegmentCounts
import RamanujanPV.QuotientCDeterminism

/-! The complete actual segmented C checker. Its claims buffer is untrusted
input, its scratch buffer is initialized by source stores, and all integer
divisors are visited. A positive completed output can therefore certify exact
classifications and count increments without assuming any prime flags. Concrete
physical executions remain subject to the documented generic C ABI/compiler,
runtime and hardware association boundary. -/
namespace RamanujanPV.SegmentCFunction
open LCMSourcePV.Witness.C LCMSourcePV.ASTLoops QuotientCMachine
open SegmentMemory SegmentCheckerMath SegmentCFunctionPrefix
set_option autoImplicit false
set_option maxHeartbeats 2000000

def countDeclaration : Stmt := .declare [⟨"uint64_t","count",some (.nat 0)⟩]
def resultExpr : Expr := .binary "+" (.var "count") (.nat 1)
def resultReturn : Stmt := .returnStmt resultExpr

theorem source_shape : SegmentCheckerSource.checkerFunction.body=
    .sequence (prefixStatements++[countDeclaration,SegmentCClaims.claimsFor,resultReturn]) := rfl

theorem seq_append {call : Service} {front back : List Stmt} {s t : State} {out : Flow}
    (first : SeqRun call front s (.continuing t)) (second : SeqRun call back t out) :
    SeqRun call (front++back) s out := by
  induction front generalizing s with
  | nil => cases first; exact second
  | cons head tail ih =>
    cases first with
    | next headRun tailRun => exact SeqRun.next headRun (ih tailRun)

theorem return_count {call : Service} {s : State} {count : Nat}
    (hcount : s.env "count"=some (.u64 count)) (hword : count+1 < modulus) :
    Run call resultReturn s (.returned s (.u64 (count+1))) := by
  have hp : evalPure call s.heap s.env 8 resultExpr=some (.u64 (count+1)) := by
    exact pure_binary_of
      ((pure_var call s.heap s.env 6 "count").trans hcount)
      ((pure_literal call s.heap s.env 6 1).trans (by norm_num [literal]))
      (by simp [binary,Value.scalar,packArithmetic,unsignedCommon,Nat.mod_eq_of_lt hword])
  apply StmtRun.returnValue
  change (do let value ← evalPure call s.heap s.env 8 resultExpr; pure (s,value))=_
  rw [hp]
  rfl

theorem correct_claims_execution {call : Service} {s : State}
    {lo hi capacity cb fb : Nat} {claims : Nat→Nat}
    (hlo : 2≤lo) (horder : lo≤hi) (hhi : hi≤2000000000000)
    (hcapacity : hi-lo+1≤capacity) (disjoint : cb≠fb)
    (owned : Owned s.heap) (buffer : SegmentCInit.Buffer s.heap fb (hi-lo+1))
    (claimRep : FlagsRep s.heap cb (hi-lo+1) claims)
    (env : Inputs lo hi capacity cb fb s.env)
    (same : ∀i,i<hi-lo+1→claims i=finalFlags lo hi i) :
    ∃ t, Run call SegmentCheckerSource.checkerFunction.body s
        (.returned t (.u64 (segmentCount lo hi+1))) ∧
      t.env=s.env ∧ Owned t.heap := by
  have lenWord : hi-lo+1 < modulus := by norm_num [modulus]; omega
  have resultWord : segmentCount lo hi+1 < modulus := by
    have bound := SegmentCounts.sum_finalFlags_le hlo horder
    rw [SegmentCounts.sum_finalFlags hlo horder] at bound
    norm_num [modulus]
    omega
  obtain ⟨prepared,prefix,envPrepared,ownedPrepared,flagRep,claimsPrepared⟩ :=
    prefix_exec hlo horder hhi hcapacity disjoint owned buffer claimRep env
  let started : State := {prepared with env:=bind prepared.env "count" (.u64 0)}
  have declaration : Declare call [⟨"uint64_t","count",some (.nat 0)⟩] prepared started :=
    declare_singleton_of (raw:=.i32 0) (by simpa [envPrepared] using env.countFresh)
      ((pure_literal call prepared.heap prepared.env 7 0).trans (by norm_num [literal]))
      (by norm_num [uint64,Value.scalar,modulus])
  have bits : ∀i,i<hi-lo+1→finalFlags lo hi i≤1 := by
    intro i hiIndex
    have bit := final_flag_zero_or_one (lo:=lo) (hi:=hi) (i:=i) hlo (by omega)
    omega
  obtain ⟨last,checks,heapLast,envLast⟩ := SegmentCClaims.matching_loop (call:=call)
    (s:=started) claimsPrepared flagRep
    (by simpa [started,envPrepared] using env.claimsValue)
    (by simpa [started,envPrepared] using env.flagsValue)
    (by simp [started]) (by simp [started,envPrepared])
    (by simpa [started,envPrepared] using env.iFresh) lenWord bits same
  have countLast : last.env "count"=some (.u64 (segmentCount lo hi)) := by
    rw [envLast]
    simp only [bind_same]
    rw [SegmentCClaims.prefixSum_eq_sum,SegmentCounts.sum_finalFlags hlo horder]
  let final := closeScope s last
  have finalEnv : final.env=s.env := by
    funext name
    by_cases hlength : name="length"
    · subst name; simp [final,closeScope,env.lengthFresh]
    · by_cases hcount : name="count"
      · subst name; simp [final,closeScope,env.countFresh]
      · change (if (s.env name).isSome then last.env name else none)=s.env name
        rw [envLast]
        simp only [started,envPrepared,QuotientCMachine.bind,Function.update_of_ne hlength,
          Function.update_of_ne hcount]
        cases h : s.env name <;> rfl
  refine ⟨final,?_,finalEnv,?_⟩
  · rw [source_shape]
    apply StmtRun.sequence (inner:=.returned last (.u64 (segmentCount lo hi+1)))
    · exact seq_append prefix (SeqRun.next (StmtRun.declare declaration)
        (SeqRun.next checks (SeqRun.returned (return_count countLast resultWord))))
    · rfl
  · simpa [final,closeScope,heapLast,started] using ownedPrepared

/-- Actual mismatch takes the source failure return, after the source has
computed its own independent classifications. This does not trust claims. -/
theorem incorrect_claims_execution {call : Service} {s : State}
    {lo hi capacity cb fb : Nat} {claims : Nat→Nat}
    (hlo : 2≤lo) (horder : lo≤hi) (hhi : hi≤2000000000000)
    (hcapacity : hi-lo+1≤capacity) (disjoint : cb≠fb)
    (owned : Owned s.heap) (buffer : SegmentCInit.Buffer s.heap fb (hi-lo+1))
    (claimRep : FlagsRep s.heap cb (hi-lo+1) claims)
    (env : Inputs lo hi capacity cb fb s.env)
    (different : ∃i,i<hi-lo+1 ∧ claims i≠finalFlags lo hi i) :
    ∃ t, Run call SegmentCheckerSource.checkerFunction.body s (.returned t (.i32 0)) := by
  have lenWord : hi-lo+1 < modulus := by norm_num [modulus]; omega
  obtain ⟨prepared,prefix,envPrepared,ownedPrepared,flagRep,claimsPrepared⟩ :=
    prefix_exec hlo horder hhi hcapacity disjoint owned buffer claimRep env
  let started : State := {prepared with env:=bind prepared.env "count" (.u64 0)}
  have declaration : Declare call [⟨"uint64_t","count",some (.nat 0)⟩] prepared started :=
    declare_singleton_of (raw:=.i32 0) (by simpa [envPrepared] using env.countFresh)
      ((pure_literal call prepared.heap prepared.env 7 0).trans (by norm_num [literal]))
      (by norm_num [uint64,Value.scalar,modulus])
  have bits : ∀i,i<hi-lo+1→finalFlags lo hi i≤1 := by
    intro i hiIndex
    have bit := final_flag_zero_or_one (lo:=lo) (hi:=hi) (i:=i) hlo (by omega)
    omega
  obtain ⟨last,reject,heapLast⟩ := SegmentCClaims.mismatching_loop (call:=call)
    (s:=started) claimsPrepared flagRep
    (by simpa [started,envPrepared] using env.claimsValue)
    (by simpa [started,envPrepared] using env.flagsValue)
    (by simp [started]) (by simp [started,envPrepared])
    (by simpa [started,envPrepared] using env.iFresh) lenWord bits different
  refine ⟨closeScope s last,?_⟩
  rw [source_shape]
  apply StmtRun.sequence (inner:=.returned last (.i32 0))
  · exact seq_append prefix (SeqRun.next (StmtRun.declare declaration) (SeqRun.returned reject))
  · rfl

/-- Positive completed outputs of the actual source certify all input bits and
the exact prime-count increment. The C function return conversion is explicit:
the literal error return has type int and converts to uint64 zero. -/
theorem positive_output_sound {call : Service} {s t : State}
    {lo hi capacity cb fb output : Nat} {claims : Nat→Nat} {raw : Value}
    (hlo : 2≤lo) (horder : lo≤hi) (hhi : hi≤2000000000000)
    (hcapacity : hi-lo+1≤capacity) (disjoint : cb≠fb)
    (owned : Owned s.heap) (buffer : SegmentCInit.Buffer s.heap fb (hi-lo+1))
    (claimRep : FlagsRep s.heap cb (hi-lo+1) claims)
    (env : Inputs lo hi capacity cb fb s.env)
    (run : Run call SegmentCheckerSource.checkerFunction.body s (.returned t raw))
    (converted : uint64 raw=some (.u64 output)) (positive : 0<output) :
    output=segmentCount lo hi+1 ∧
      (∀i,i<hi-lo+1→claims i=if Nat.Prime (lo+i) then 1 else 0) ∧
      Nat.primeCounting hi=Nat.primeCounting (lo-1)+(output-1) := by
  classical
  by_cases same : ∀i,i<hi-lo+1→claims i=finalFlags lo hi i
  · obtain ⟨expected,correct,envExpected,ownedExpected⟩ :=
      correct_claims_execution hlo horder hhi hcapacity disjoint owned buffer claimRep env same
    have equal := (QuotientCDeterminism.returned_unique run correct).2
    have resultWord : segmentCount lo hi+1 < modulus := by
      have bound := SegmentCounts.sum_finalFlags_le hlo horder
      rw [SegmentCounts.sum_finalFlags hlo horder] at bound
      norm_num [modulus]
      omega
    have outputEq : output=segmentCount lo hi+1 := by
      rw [equal,uint64_of_u64 resultWord] at converted
      exact (Value.u64.inj (Option.some.inj converted)).symm
    refine ⟨outputEq,?_,?_⟩
    · intro i hiIndex
      rw [same i hiIndex,final_flag hlo (by omega)]
    · rw [outputEq,Nat.add_sub_cancel]
      exact primeCounting_increment hlo horder
  · have mismatch : ∃i,i<hi-lo+1 ∧ claims i≠finalFlags lo hi i := by
      simpa only [not_forall,not_imp] using same
    obtain ⟨expected,reject⟩ :=
      incorrect_claims_execution hlo horder hhi hcapacity disjoint owned buffer claimRep env mismatch
    have equal := (QuotientCDeterminism.returned_unique run reject).2
    rw [equal] at converted
    have zero : output=0 := by
      simpa [uint64,Value.scalar,modulus] using (Option.some.inj converted).symm
    omega

#print axioms source_shape
#print axioms correct_claims_execution
#print axioms incorrect_claims_execution
#print axioms positive_output_sound
end RamanujanPV.SegmentCFunction
