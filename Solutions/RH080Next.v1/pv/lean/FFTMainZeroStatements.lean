/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTMainInitializedView
import FFTRecursiveSegments
import FFTStatusCall
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.MainAllocation
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings ApplicationBirthFrame RecursiveSource

def zeroStatement (r : Role) : Stmt:=.expression (.call "zero_words" [.variable (name r),countExpr r])
def zeroPrefix : List Stmt:=[.output,.data,.twiddle,.work].map zeroStatement

theorem actual_w4_zero_prefix : ((bodyItems FFTRecursivePV.w4_recursive_norm_upper_ast).drop 8).take 4=zeroPrefix := by rfl
theorem actual_fap_zero_prefix : ((bodyItems FapFFTRecursivePV.fap_recursive_norm_upper_ast).drop 8).take 4=zeroPrefix := by rfl

theorem InitializedView.count_eval {F : Type} (context : Context F) {state : State F}
    {n nId owner : Nat} {objects ids : Role → Nat} {done : List Role}
    (h : InitializedView state n nId owner objects ids done) (small : n≤2^24) (r : Role) :
    Eval context state (countExpr r) (.integer (integer64 (length n r))) state := by
  have fit : n<2^64 := by omega
  have nEval : Eval context state (.variable "n") (.integer (integer64 n)) state :=
    .variable (h.locals.lookup none) (h.locals.read none)
  have lit12 : Eval context state (RecursiveSource.literal 12) (.integer (integer64 12)) state :=
    .literal (.integer 12 "ULL") _ (.integer (integer64 12)) (by rfl)
  have productFit : n*12<2^64 := by omega
  cases r with
  | data => exact mul_expr_eval context nEval lit12 fit (by norm_num) productFit
  | output => exact mul_expr_eval context nEval lit12 fit (by norm_num) productFit
  | work => exact .literal (.integer 512 "ULL") _ (.integer (integer64 512)) (by rfl)
  | twiddle =>
    have half:=div_expr_eval context nEval
      (Eval.literal (.integer 2 "ULL") _ (.integer (integer64 2)) (by rfl)) fit (by norm_num) (by decide)
    exact mul_expr_eval context half lit12 (by omega) (by norm_num) (by omega)

theorem zero_arguments_pure (r : Role) : ∀e∈[.variable (name r),countExpr r],SourcePure.CallFree e := by
  cases r <;> simp [countExpr,SourcePure.CallFree,mulExpr,literal]

/-- Actual source expression call and all permitted argument orders. -/
theorem InitializedView.zero_step {F : Type} (context : Context F) {before : State F}
    {n nId owner : Nat} {objects ids : Role → Nat} {done : List Role} (r : Role)
    (h : InitializedView before n nId owner objects ids done) (notDone : r∉done) (small : n≤2^24)
    (selected : findFunction context.program "zero_words"=some zero_words_ast) :
    ∃after,NormalSegment context before [zeroStatement r] after ∧
      InitializedView after n nId owner objects ids (r::done) ∧
      ZeroRaw.FullCallerFrame before after (objects r) := by
  have raw : before.objects (objects r)=some (zeroPrefixObject (length n r) 0) := by
    simpa only [MemoryReady,if_neg notDone] using h.memory r
  have fit : length n r<2^64 := by have bound:=length_bytes_fit small r;omega
  obtain ⟨after,called,words,frame⟩:=ZeroRaw.zero_words_call_framed context selected before
    (objects r) (length n r) h.well h.host raw fit
  have args : Args context before [.variable (name r),countExpr r]
      [.pointer (wordPointer (objects r) 0),.integer (integer64 (length n r))] before :=
    .ordered (List.Perm.refl _)
      (.cons (.variable (h.locals.lookup (some r)) (h.locals.read (some r)))
        (.cons (h.count_eval context small r) .nil)) (.cons rfl (.cons rfl .nil))
  have everyCall : ∀other result,Call context "zero_words"
      [.pointer (wordPointer (objects r) 0),.integer (integer64 (length n r))] before result other →
      result=.value (.integer (integer64 0)) ∧ other=after := by
    intro other result actual
    exact ZeroCallUnique.returned_call_unique selected called actual
  have every : ∀other flow,Exec context before (zeroStatement r) flow other → flow=.normal ∧ other=after := by
    intro other flow actual
    cases actual with
    | expression ev =>
      obtain ⟨rfl,rfl⟩:=StatusCall.call_eval_unique (zero_arguments_pure r) args everyCall ev
      exact ⟨rfl,rfl⟩
    | callTerminated ar ca =>
      obtain ⟨_,rfl,rfl⟩:=ApplicationPureCall.args_unique (zero_arguments_pure r) args ar
      have impossible:=(everyCall _ _ ca).1
      cases impossible
  exact ⟨after,.single (.expression (.call args called)) every,h.after_zero notDone frame words,frame⟩

/-- All four source loops establish the complete typed initial memory. -/
theorem InitializedView.all_zero_steps {F : Type} (context : Context F) {before : State F}
    {n nId owner : Nat} {objects ids : Role → Nat}
    (h : InitializedView before n nId owner objects ids []) (small : n≤2^24)
    (selected : findFunction context.program "zero_words"=some zero_words_ast) :
    ∃after,NormalSegment context before zeroPrefix after ∧
      InitializedView after n nId owner objects ids [.work,.twiddle,.data,.output] ∧
      Frame before.nextObject before after [objects .output,objects .data,objects .twiddle,objects .work] := by
  obtain ⟨s1,r1,h1,f1⟩:=h.zero_step context .output (by simp) small selected
  obtain ⟨s2,r2,h2,f2⟩:=h1.zero_step context .data (by simp) small selected
  obtain ⟨s3,r3,h3,f3⟩:=h2.zero_step context .twiddle (by simp) small selected
  obtain ⟨after,r4,h4,f4⟩:=h3.zero_step context .work (by simp) small selected
  have widen {a b : State F} {cutoff object : Nat} (f : Frame cutoff a b [object])
      (member : object∈[objects .output,objects .data,objects .twiddle,objects .work]) :
      Frame cutoff a b [objects .output,objects .data,objects .twiddle,objects .work] := by
    refine ⟨f.well,f.fresh,f.nextObject,f.nextScope,f.mode,f.foreign,?_⟩
    intro id old absent
    apply f.outside id old
    intro same
    have eq : id=object:=by simpa using same
    exact absent (eq ▸ member)
  have a:=widen (f1.birth (le_refl _)) (by simp)
  have b:=widen (f2.birth a.fresh) (by simp)
  have c:=widen (f3.birth b.fresh) (by simp)
  have d:=widen (f4.birth c.fresh) (by simp)
  exact ⟨after,((r1.append r2).append r3).append r4,h4,((a.trans b).trans c).trans d⟩

#print axioms InitializedView.zero_step
#print axioms InitializedView.all_zero_steps
end RH080Next.FFTPV.MainAllocation
