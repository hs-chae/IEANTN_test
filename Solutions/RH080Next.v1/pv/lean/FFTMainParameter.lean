/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTMainInitialization
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.MainAllocation
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings ApplicationBirthFrame

/-- The actual norm parameter is allocated by the real bindParameters rule,
not supplied as an initialized application-local-state assumption. -/
theorem bind_norm_parameter {F : Type} {caller : State F} (n : Nat)
    (well : WellScoped caller) (fit : n<2^64) :
    ∃entered,bindParameters {caller.enterScope with environment:=[]} [(.u64,"n")]
        [.integer (integer64 n)]=some entered ∧
      entered.environment.lookup "n"=some (scalarPointer caller.nextObject .u64) ∧
      Slot entered caller.nextObject caller.nextScope .u64 (.integer (integer64 n)) ∧
      WellScoped entered ∧ entered.scope=caller.nextScope ∧
      entered.mode=caller.mode ∧ entered.nextObject=caller.nextObject+1 ∧
      entered.nextScope=caller.nextScope+1 ∧
      Frame caller.nextObject caller.enterScope entered [] := by
  let entry : State F:={caller.enterScope with environment:=[]}
  have we:WellScoped entry:=wellScoped_environment (wellScoped_enter well) []
  have storage:=ZeroFrame.u64_storable n fit
  obtain ⟨entered,declared⟩:=ZeroFrame.declare_exists we .u64 "n" (.integer (integer64 n)) storage
  have d:=declare_storable storage storage.converted declared
  refine ⟨entered,?_,?_,?_,wellScoped_declare we declared,?_,?_,?_,?_,?_⟩
  · change bindParameters entry [(.u64,"n")] [.integer (integer64 n)]=some entered
    simp [bindParameters,declared]
  · rw [d.environment]
    simp [entry,List.lookup,State.enterScope]
  · exact d.slot
  · exact d.scope
  · exact d.mode
  · exact d.nextObject
  · exact d.nextScope
  · have f:=declare_frame caller.nextObject [] we (le_refl _) declared
    exact ⟨f.well,f.fresh,f.nextObject,f.nextScope,f.mode,f.foreign,f.outside⟩

/-- Complete actual source prefix including its real function parameter birth. -/
theorem entered_source_initialization {F : Type} (context : Context F) (caller : State F) (n : Nat)
    (well : WellScoped caller) (host : caller.mode=.host) (small : n≤2^24)
    (absent : findFunction context.program "calloc"=none) (memory : HasMemory context)
    (selected : findFunction context.program "zero_words"=some zero_words_ast) :
    ∃entered after objects ids,
      bindParameters {caller.enterScope with environment:=[]} [(.u64,"n")]
        [.integer (integer64 n)]=some entered ∧
      ExecList context entered initializationPrefix .normal after ∧
      InitializedView after n caller.nextObject caller.nextScope objects ids [.work,.twiddle,.data,.output] ∧
      (∀r,WordArrayRep after (objects r) (length n r) (fun _=>0)) ∧
      Frame caller.nextObject caller.enterScope after [] := by
  obtain ⟨entered,bound,lookup,slot,we,scope,mode,no,ns,parameterFrame⟩:=bind_norm_parameter n well (by omega)
  obtain ⟨after,objects,ids,run,ready,words,frame,future⟩:=source_initialization context lookup slot we
    (mode.trans host) scope small absent memory selected
  exact ⟨entered,after,objects,ids,bound,run,ready,words,
    parameterFrame.trans (lower_cutoff frame parameterFrame.nextObject)⟩

#print axioms bind_norm_parameter
#print axioms entered_source_initialization
end RH080Next.FFTPV.MainAllocation
