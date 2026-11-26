/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTRootCall
import ExplicitFFTAddSource
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.RootSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals

/-- Complete actual helper contract. The caller establishes only a live typed
array and a safe layout. All application initialization, source arithmetic,
termination, model equality and temporary/caller lifetime obligations are proved.
Consumption by the complete numerical ANT pipeline is a separate obligation. -/
def RootCorrect {F : Type} (context : Context F) (before : State F) (input : Input) : Prop:=
  ∃after finalData,Call context "initialize_root" (arguments input) before (.value (.integer (integer64 0))) after ∧
    EveryCall context before "initialize_root" (arguments input) (.value (.integer (integer64 0))) after ∧
    WordArrayRep after input.layout.object input.layout.size finalData ∧
    FixedValue finalData input.layout.rootStart (taylorState input.n 10).cr ∧
    FixedValue finalData (input.layout.rootStart+6) (-(taylorState input.n 10).sr) ∧
    (CanonicalSource.represented finalData input.layout.rootStart,CanonicalSource.represented finalData (input.layout.rootStart+6))=
      FFT.IntegerModel.root input.n ∧
    IncrementSource.FullCallerFrame before after input.layout.object ∧
    ∀k,k< input.layout.size → (k< input.layout.workStart ∨ input.layout.workStart+80≤ k) →
      (k< input.layout.rootStart ∨ input.layout.rootStart+12≤ k) → finalData k=input.old k

theorem initialize_root_total {F : Type} (context : Context F) (functions : Functions context)
    (selected : findFunction context.program "initialize_root"=some initialize_root_ast)
    (before : State F) (input : Input) (grid : OriginalGrid input.n) (well : WellScoped before)
    (rep : WordArrayRep before input.layout.object input.layout.size input.old) : RootCorrect context before input:=
  initialize_root_call context functions selected before input grid well rep

/-- The real application allocates 512 words, with its root at work+128.
This is an instance of the same-object slice contract, not an assumed initialized
workspace or a replacement allocation model. -/
def originalLayout (object : Nat) : Layout:=
  ⟨object,512,128,0,by omega,by omega,Or.inr (by omega)⟩

def originalInput (object : Nat) (old : Nat → Nat) (n : Nat) (grid : OriginalGrid n) : Input:=
  ⟨originalLayout object,old,n,(original_grid_divisor n grid).1,(original_grid_divisor n grid).2⟩

theorem source_initialize_root_total (before : State Unit) (input : Input) (grid : OriginalGrid input.n)
    (well : WellScoped before) (rep : WordArrayRep before input.layout.object input.layout.size input.old) :
    Correspondence.SourceSyntaxCorresponds RH080Next.FFTPV.source RH080Next.FFTPV.program ∧
      RootCorrect CompareSource.sourceContext before input:=
  ⟨RH080Next.FFTPV.actual_source_syntax,initialize_root_total _ (by constructor <;> rfl) (by rfl) before input grid well rep⟩

theorem fap_source_initialize_root_total (before : State Unit) (input : Input) (grid : OriginalGrid input.n)
    (well : WellScoped before) (rep : WordArrayRep before input.layout.object input.layout.size input.old) :
    Correspondence.SourceSyntaxCorresponds RH080Next.FapFFTPV.source RH080Next.FapFFTPV.program ∧
      RootCorrect CompareSource.fapSourceContext before input:=
  ⟨RH080Next.FapFFTPV.actual_source_syntax,initialize_root_total _ (by constructor <;> rfl) (by rfl) before input grid well rep⟩

theorem recursive_source_initialize_root_total (before : State Unit) (input : Input) (grid : OriginalGrid input.n)
    (well : WellScoped before) (rep : WordArrayRep before input.layout.object input.layout.size input.old) :
    Correspondence.SourceSyntaxCorresponds FFTRecursivePV.source FFTRecursivePV.program ∧
      RootCorrect AddSource.recursiveContext before input:=
  ⟨FFTRecursivePV.actual_source_syntax,initialize_root_total _ (by constructor <;> rfl) (by rfl) before input grid well rep⟩

theorem fap_recursive_source_initialize_root_total (before : State Unit) (input : Input) (grid : OriginalGrid input.n)
    (well : WellScoped before) (rep : WordArrayRep before input.layout.object input.layout.size input.old) :
    Correspondence.SourceSyntaxCorresponds FapFFTRecursivePV.source FapFFTRecursivePV.program ∧
      RootCorrect AddSource.fapRecursiveContext before input:=
  ⟨FapFFTRecursivePV.actual_source_syntax,initialize_root_total _ (by constructor <;> rfl) (by rfl) before input grid well rep⟩

#print axioms initialize_root_total
#print axioms source_initialize_root_total
#print axioms fap_source_initialize_root_total
#print axioms recursive_source_initialize_root_total
#print axioms fap_recursive_source_initialize_root_total
end RH080Next.FFTPV.RootSource
