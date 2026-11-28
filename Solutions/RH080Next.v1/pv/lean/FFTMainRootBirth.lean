/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTMainRootBirthTotal
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
namespace RH080Next.FFTPV.MainRootBirth
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings ApplicationBirthFrame
open MainAllocation

def initializedRootPrefix : List Stmt:=initializationPrefix++rootBirthStatements

theorem actual_w4_initialized_root_prefix : (bodyItems FFTRecursivePV.w4_recursive_norm_upper_ast).take 17=initializedRootPrefix := by rfl
theorem actual_fap_initialized_root_prefix : (bodyItems FapFFTRecursivePV.fap_recursive_norm_upper_ast).take 17=initializedRootPrefix := by rfl

private theorem append_execution {F : Type} {context : Context F} {before middle after : State F}
    {xs ys : List Stmt} (first : ExecList context before xs .normal middle)
    (second : ExecList context middle ys .normal after) : ExecList context before (xs++ys) .normal after := by
  induction xs generalizing before with
  | nil=>cases first;exact second
  | cons x xs ih=>
    cases first with
    | cons head tail=>exact .cons head (ih tail)
    | abrupt head impossible=>exact False.elim (impossible rfl)

/-- Actual source entry and first17 main instructions from an arbitrary
well-scoped host caller: real n binding, calloc/null/zero prefix, pointer births,
initializer Call and status birth. No initialized root/status/local is assumed.
The first12 success branch is selected; whole-main failure classification is
proved separately by the allocation/main owner. -/
theorem entered_source_root_initialization {F : Type} (context : Context F)
    (functions : RootSource.Functions context)
    (selected : findFunction context.program "initialize_root"=some initialize_root_ast)
    (caller : State F) (n : Nat) (grid : RootSource.OriginalGrid n)
    (well : WellScoped caller) (host : caller.mode=.host)
    (absent : findFunction context.program "calloc"=none) (memory : HasMemory context) :
    ∃entered after objects oldIds base status workData,
      bindParameters {caller.enterScope with environment:=[]} [(.u64,"n")]
        [.integer (integer64 n)]=some entered ∧
      ExecList context entered initializedRootPrefix .normal after ∧
      Ready after n caller.nextObject caller.nextScope objects oldIds base status workData ∧
      Frame caller.nextObject caller.enterScope after [objects .work] := by
  have small : n≤2^24 := by rcases grid with rfl|rfl <;> norm_num
  obtain ⟨entered,before,objects,oldIds,bound,initialization,h,zeroArrays,prefixFrame⟩:=
    entered_source_initialization context caller n well host small absent memory functions.zero
  obtain ⟨after,status,workData,births,ready,frame⟩:=from_initialized context functions selected h grid
  have first : Frame caller.nextObject caller.enterScope before [objects .work] :=
    ⟨prefixFrame.well,prefixFrame.fresh,prefixFrame.nextObject,prefixFrame.nextScope,prefixFrame.mode,prefixFrame.foreign,
      fun id old _=>prefixFrame.outside id old (by simp)⟩
  have last : Frame caller.nextObject before after [objects .work] :=
    ⟨frame.well,prefixFrame.nextObject.trans frame.fresh,frame.nextObject,frame.nextScope,frame.mode,frame.foreign,
      fun id old absent=>frame.outside id (old.trans_le prefixFrame.nextObject) absent⟩
  exact ⟨entered,after,objects,oldIds,before.nextObject,status,workData,bound,
    append_execution initialization births.execution,ready,first.trans last⟩

#print axioms entered_source_root_initialization
end RH080Next.FFTPV.MainRootBirth
