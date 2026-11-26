/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTInputLoaderLoop
import ExplicitFFTInputLoaderIntegerInput
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.InputLoader
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings
open RootSource

def Profile.source : Profile → String
  | .fap=> FapFFTRecursivePV.source
  | .w4=> FFTRecursivePV.source

def Profile.mainFunction : Profile → Function
  | .fap=> FapFFTRecursivePV.fap_recursive_norm_upper_ast
  | .w4=> FFTRecursivePV.w4_recursive_norm_upper_ast

theorem Profile.actual_syntax (p : Profile) : Correspondence.SourceSyntaxCorresponds p.source p.program:=by
  cases p with
  | fap=> exact FapFFTRecursivePV.actual_source_syntax
  | w4=> exact FFTRecursivePV.actual_source_syntax

theorem Profile.source_loop (p : Profile) : (ProductRow.items p.mainFunction.body)[21]?=some (loop p.count):=by
  cases p with
  | fap=> exact actual_fap_input_loop
  | w4=> exact actual_w4_input_loop

/-- The real main path must establish the zeroed typed allocation and its
three actual source variables. This segment constructs the complete input
loop execution; it never assumes an already-computed input vector. -/
def Correct {F : Type} (context : Context F) (before : State F) (input : Input) (fo : Nat) (ids : Parameter → Nat) : Prop:=
  ∃after,Exec context before (loop input.profile.count) .normal after ∧
    Every context before (loop input.profile.count) .normal after ∧
    WordArrayRep after input.object (12*input.profile.grid) (currentData input.profile.encoded input.profile.grid input.profile.count) ∧
    Locals after parameterName parameterType ids fo (parameterValues input input.profile.count) ∧
    MultiplyCall.CallerFrame before after [input.object,ids .j] ∧
    ∀k< input.profile.grid,
      ComplexSource.pair (currentData input.profile.encoded input.profile.grid input.profile.count) (12*k)=input.profile.mathematicalInput k

theorem input_loader_total {F : Type} (context : Context F) (before : State F) (input : Input) (fo : Nat) (ids : Parameter → Nat)
    (pinned : context.program=input.profile.program) (well : WellScoped before)
    (array : WordArrayRep before input.object (12*input.profile.grid) (fun _=>0))
    (locals : Locals before parameterName parameterType ids fo (parameterValues input 0)) (separate : ∀p,input.object≠ids p) :
    Correct context before input fo ids:=by
  have initial : LoopView before input fo ids 0:=⟨array,locals,separate,by omega,well⟩
  obtain ⟨after,run,every,post,frame,env,scope⟩:=loop_execution context input.profile.count initial pinned (by omega) (le_refl _)
  exact ⟨after,run,every,post.array,post.locals,⟨env,scope,frame⟩,completed_input_pair input.profile⟩

/-- Independent syntax and the actual source-main locator are consumed by the
source segment's model refinement. Complete main/FFT/ANT consumption is separate. -/
theorem source_input_loader_total {F : Type} (context : Context F) (before : State F) (input : Input) (fo : Nat) (ids : Parameter → Nat)
    (pinned : context.program=input.profile.program) (well : WellScoped before)
    (array : WordArrayRep before input.object (12*input.profile.grid) (fun _=>0))
    (locals : Locals before parameterName parameterType ids fo (parameterValues input 0)) (separate : ∀p,input.object≠ids p) :
    Correspondence.SourceSyntaxCorresponds input.profile.source input.profile.program ∧
      (ProductRow.items input.profile.mainFunction.body)[21]?=some (loop input.profile.count) ∧
      Correct context before input fo ids:=
  ⟨input.profile.actual_syntax,input.profile.source_loop,input_loader_total context before input fo ids pinned well array locals separate⟩

#print axioms input_loader_total
#print axioms source_input_loader_total
end RH080Next.FFTPV.InputLoader
