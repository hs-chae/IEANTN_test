/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTZeroGenericCall
import FFTZeroTrace
import ExplicitApplicationBirthFrame
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.MainAllocation
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings ApplicationBirthFrame

/-- The generic calloc contract has no application-state or output premise. -/
def HasMemory {F : Type} (context : Context F) : Prop :=
  ∀operation args before result after,PlatformMemory.Call F operation args before result after →
    context.foreign (.call operation) args before (.value result) after

def callocExpr (count : Expr) : Expr :=
  .cast (.pointer .u64) (.call "calloc" [count,.literal (.integer 8 "ULL")])

/-- The source can receive NULL as permitted by the same generic API model.
This branch remains present; no theorem assumes calloc always succeeds. -/
theorem calloc_failure {F : Type} (context : Context F) {before : State F}
    {countExpr : Expr} {length : Nat}
    (absent : findFunction context.program "calloc"=none) (memory : HasMemory context)
    (fit : length<2^64)
    (countEval : Eval context before countExpr (.integer (integer64 length)) before) :
    Eval context before (callocExpr countExpr) .null before := by
  have size : PlatformMemory.sizeArgument (.integer (integer64 length))=some length := by
    dsimp only [PlatformMemory.sizeArgument]
    rw [integer64_toInt,cast64_exact length fit]
    rfl
  have width : PlatformMemory.sizeArgument (.integer (integer64 8))=some 8 := by decide
  have args : Args context before [countExpr,.literal (.integer 8 "ULL")]
      [.integer (integer64 length),.integer (integer64 8)] before :=
    .ordered (List.Perm.refl _) (.cons countEval
      (.cons (.literal (.integer 8 "ULL") _ (.integer (integer64 8)) (by rfl)) .nil))
      (.cons rfl (.cons rfl .nil))
  exact .cast (.call args (.external absent rfl (memory _ _ _ _ _ (.callocFailure before _ _ _ _ size width)))) rfl

/-- A fresh generic byte allocation and its actual cast expression. The raw
bytes are not a typed WordArrayRep; zero_words will establish that separately. -/
theorem calloc_success {F : Type} (context : Context F) {before : State F}
    {countExpr : Expr} {length : Nat}
    (absent : findFunction context.program "calloc"=none) (memory : HasMemory context)
    (well : WellScoped before) (host : before.mode=.host) (byteFit : length*8<2^64)
    (countEval : Eval context before countExpr (.integer (integer64 length)) before) :
    ∃after,Eval context before (callocExpr countExpr)
        (.pointer (wordPointer before.nextObject 0)) after ∧
      after.objects before.nextObject=some (zeroPrefixObject length 0) ∧
      Frame before.nextObject before after [] ∧
      after.environment=before.environment ∧ after.scope=before.scope := by
  have fit : length<2^64 := by omega
  have fresh : before.objects before.nextObject=none := by
    cases present : before.objects before.nextObject with
    | none => rfl
    | some obj => have impossible:=well.objectIds _ _ present;omega
  let after : State F := {before with
    objects:=fun id=>if id=before.nextObject then
      some ⟨8*length,true,.host,PlatformMemory.zeroBytes (8*length)⟩ else before.objects id,
    nextObject:=before.nextObject+1}
  have born : before.allocate .host (8*length) (PlatformMemory.zeroBytes (8*length))=
      some (⟨before.nextObject,0,.void⟩,after) := by simp [State.allocate,fresh,after]
  have size : PlatformMemory.sizeArgument (.integer (integer64 length))=some length := by
    dsimp only [PlatformMemory.sizeArgument]
    rw [integer64_toInt,cast64_exact length fit]
    rfl
  have width : PlatformMemory.sizeArgument (.integer (integer64 8))=some 8 := by decide
  have called : Call context "calloc" [.integer (integer64 length),.integer (integer64 8)] before
      (.value (.pointer ⟨before.nextObject,0,.void⟩)) after :=
    .external absent rfl (memory _ _ _ _ _ (.callocSuccess _ _ _ _ _ _ _ size width byteFit
      (by simpa only [Nat.mul_comm] using born)))
  have args : Args context before [countExpr,.literal (.integer 8 "ULL")]
      [.integer (integer64 length),.integer (integer64 8)] before :=
    .ordered (List.Perm.refl _) (.cons countEval
      (.cons (.literal (.integer 8 "ULL") _ (.integer (integer64 8)) (by rfl)) .nil))
      (.cons rfl (.cons rfl .nil))
  have raw:=WordArrays.calloc_prefix_zero host born
  have wa:=wellScoped_allocate well (by intro owner impossible;cases impossible) born
  refine ⟨after,.cast (.call args called) (by rfl),raw.2,?_,rfl,rfl⟩
  refine ⟨wa,by dsimp [after];omega,by dsimp [after];omega,le_refl _,rfl,rfl,?_⟩
  intro id old _
  simp only [after]
  rw [if_neg (by omega)]

#print axioms calloc_failure
#print axioms calloc_success
end RH080Next.FFTPV.MainAllocation
