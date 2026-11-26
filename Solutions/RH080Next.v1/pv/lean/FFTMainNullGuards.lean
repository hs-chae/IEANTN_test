/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTMainZeroStatements
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.MainAllocation
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings ApplicationBirthFrame RecursiveSource

def nullTest (r : Role) : Expr:=.binary .eq (.variable (name r)) (.literal .nullPointer)
def earlierNames : Role → List String
  | .data=>[] | .twiddle=>["data"] | .work=>["data","twiddle"] | .output=>["data","twiddle","work"]
def freeStatement (cname : String) : Stmt:=.expression (.call "free" [.variable cname])
def failureReturn : Stmt:=.returnValue (some (.literal (.integer 18446744073709551615 "ULL")))
def nullGuard (r : Role) : Stmt:=.ite (nullTest r)
  (.block ((earlierNames r).map freeStatement++[failureReturn])) none

def guardPrefix : List Stmt:=[.data,.twiddle,.work,.output].map nullGuard

theorem actual_w4_guard_prefix : ((bodyItems FFTRecursivePV.w4_recursive_norm_upper_ast).drop 4).take 4=guardPrefix := by rfl
theorem actual_fap_guard_prefix : ((bodyItems FapFFTRecursivePV.fap_recursive_norm_upper_ast).drop 4).take 4=guardPrefix := by rfl

theorem InitializedView.nonnull_test {F : Type} (context : Context F) {state : State F}
    {n nId owner : Nat} {objects ids : Role → Nat} {done : List Role}
    (h : InitializedView state n nId owner objects ids done) (r : Role) :
    Eval context state (nullTest r) (.integer (.boolean false)) state := by
  exact .binaryLR (.variable (h.locals.lookup (some r)) (h.locals.read (some r)))
    (.literal .nullPointer _ .null (by rfl)) (by rfl)

/-- All source null tests and all operand evaluation orders on the actually
allocated pointer branch. It assumes no body or free-call correctness. -/
theorem InitializedView.guard_step {F : Type} (context : Context F) {state : State F}
    {n nId owner : Nat} {objects ids : Role → Nat} {done : List Role}
    (h : InitializedView state n nId owner objects ids done) (r : Role) :
    NormalSegment context state [nullGuard r] state := by
  have test:=h.nonnull_test context r
  refine .single (.ifFalse test (by rfl)) ?_
  intro other flow actual
  cases actual with
  | ifFalse ev truth =>
    obtain ⟨rfl,rfl⟩:=PureDeterminism.eval_unique (by trivial) test ev
    exact ⟨rfl,rfl⟩
  | ifTrue ev truth body =>
    obtain ⟨rfl,rfl⟩:=PureDeterminism.eval_unique (by trivial) test ev
    cases truth

theorem InitializedView.all_guard_steps {F : Type} (context : Context F) {state : State F}
    {n nId owner : Nat} {objects ids : Role → Nat} {done : List Role}
    (h : InitializedView state n nId owner objects ids done) :
    NormalSegment context state guardPrefix state :=
  (((h.guard_step context .data).append (h.guard_step context .twiddle)).append
    (h.guard_step context .work)).append (h.guard_step context .output)

#print axioms actual_w4_guard_prefix
#print axioms actual_fap_guard_prefix
#print axioms InitializedView.all_guard_steps
end RH080Next.FFTPV.MainAllocation
