/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTRecursiveHeaderExpressions
import FFTRecursiveSegments
import FFTFixedMultiplyParameters
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.RecursiveSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings ProductInner ApplicationBirthFrame
namespace Header

theorem View.birth {F : Type} (context : Context F) {before : State F}
    {total : Nat} {buffers : Buffers total} {start index step n count owner cutoff : Nat}
    {ids : LoopVar → Nat} {input table output work : Nat → Nat} {next : LocalVar} {expr : Expr}
    (h : View before buffers start index step n count ids owner input table output work)
    (indexNext : localIndex next=count) (fresh : cutoff≤before.nextObject)
    (storable : Storable (localType next) (loopValue buffers start index step n 0 (.inr next)))
    (eval : Eval context before expr (loopValue buffers start index step n 0 (.inr next)) before)
    (pureExpr : SourcePure.CallFree expr) :
    ∃after, NormalSegment context before [.declare (localType next) (localName next) (some expr)] after ∧
      View after buffers start index step n (count+1)
        (Function.update ids (.inr next) before.nextObject) owner input table output work ∧
      Frame cutoff before after [] := by
  obtain ⟨after,declared⟩ := ZeroFrame.declare_exists h.well _ _ _ storable
  have d := declare_storable storable storable.converted declared
  have exec : Exec context before (.declare (localType next) (localName next) (some expr)) .normal after :=
    .declareSome eval declared
  refine ⟨after,NormalSegment.pure (.cons exec .nil) ?_,h.declare indexNext d declared,
    ApplicationBirthFrame.declare_frame cutoff [] h.well fresh declared⟩
  intro s hs
  have eq : s=.declare (localType next) (localName next) (some expr) := List.mem_singleton.mp hs
  subst s
  exact pureExpr

theorem View.half_birth {F : Type} (context : Context F) {before : State F}
    {total : Nat} {buffers : Buffers total} {start index step n owner cutoff : Nat}
    {ids : LoopVar → Nat} {input table output work : Nat → Nat}
    (h : View before buffers start index step n 0 ids owner input table output work)
    (hn : n<2^64) (fresh : cutoff≤before.nextObject) :
    ∃after, NormalSegment context before [halfDeclaration] after ∧
      View after buffers start index step n 1 (Function.update ids (.inr .half) before.nextObject)
        owner input table output work ∧ Frame cutoff before after [] := by
  exact h.birth context (next:=.half) rfl fresh (ZeroFrame.u64_storable (n/2) (by omega))
    (h.half_expr context hn) (by simp [SourcePure.CallFree,literal])

theorem View.tail_births {F : Type} (context : Context F) {before : State F}
    {total : Nat} {buffers : Buffers total} {start index step n owner cutoff : Nat}
    {ids : LoopVar → Nat} {input table output work : Nat → Nat}
    (h : View before buffers start index step n 2 ids owner input table output work)
    (shape : IndexShape start index step n total) (fresh : cutoff≤before.nextObject) :
    ∃after finalIds, NormalSegment context before [strideDeclaration,jDeclaration,tempDeclaration] after ∧
      LoopView after buffers start index step n finalIds owner 0 input table output work ∧
      Frame cutoff before after [] := by
  have bounds := shape.scalar_bounds
  have strideFit : total/n<2^64 := (Nat.div_le_self total n).trans_lt bounds.2.2.2.2
  have strideE := div_expr_eval context (h.parameter context .total) (h.parameter context .n)
    bounds.2.2.2.2 bounds.2.2.2.1 shape.positive
  obtain ⟨s1,run1,h1,f1⟩ := h.birth context (next:=.stride) rfl fresh
    (ZeroFrame.u64_storable (total/n) strideFit) strideE (by simp [SourcePure.CallFree])
  obtain ⟨s2,run2,h2,f2⟩ := h1.birth context (next:=.j) rfl f1.fresh
    (ZeroFrame.u64_storable 0 (by norm_num))
    (Eval.literal (.integer 0 "ULL") _ (.integer (integer64 0)) (by rfl)) (by trivial)
  have pointerE : Eval context s2 (pointerOffset "work" 160)
      (.pointer (wordPointer (buffers.object .work) 160)) s2 := by
    apply Eval.paren
    refine .binaryLR (h2.parameter context .work)
      (.literal (.integer 160 "ULL") _ (.integer (integer64 160)) (by rfl)) ?_
    have added := slice_pointer_add (start:=0) (i:=160) (h2.arrays .work) (by have hb:=buffers.workBound;omega)
    simpa only [binary,Option.map_some,Nat.zero_add,value] using congrArg (Option.map Value.pointer) added
  obtain ⟨after,run3,h3,f3⟩ := h2.birth context (next:=.temp) rfl f2.fresh
    (MultiplyParameters.pointer_storable (buffers.object .work) 160) pointerE
    (by simp [SourcePure.CallFree,pointerOffset,addExpr,literal])
  exact ⟨after,_,(run1.append run2).append run3,h3.complete,(f1.trans f2).trans f3⟩

#print axioms View.birth
#print axioms View.half_birth
#print axioms View.tail_births
end Header
end RH080Next.FFTPV.RecursiveSource
