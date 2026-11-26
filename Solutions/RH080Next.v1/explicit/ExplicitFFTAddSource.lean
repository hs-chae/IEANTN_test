/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTAddDeterminism
import ExplicitFFTAddMath
import FapFFTRecursiveSource
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.AddSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals
open IncrementSource (base)

def AddContract {F : Type} (context : Context F) (before : State F) (input : Input) : Prop:=
  ∃after,Call context "fixed_add" (arguments input) before (.value (.integer (integer64 (rawStatus input)))) after ∧
    WordArrayRep after (input.layout.object .out) (input.layout.length (input.layout.object .out)) (finalData input) ∧
    IncrementSource.FullCallerFrame before after (input.layout.object .out) ∧
    ∀after' result,Call context "fixed_add" (arguments input) before result after' →
      result=.value (.integer (integer64 (rawStatus input))) ∧ after'=after

def AddCorrect {F : Type} (context : Context F) (before : State F) (input : Input) : Prop:=
  AddContract context before input ∧ rawStatus input ≤ 1 ∧
    (∀i < 5,finalData input (input.layout.start .out+i) < base) ∧
    finalData input (input.layout.start .out+5) ≤ 1 ∧
    (rawStatus input=0 → CanonicalSource.represented (finalData input) (input.layout.start .out)=
      if 0 < input.subtract then
        CanonicalSource.represented (input.old (input.layout.object .a)) (input.layout.start .a)-
          CanonicalSource.represented (input.old (input.layout.object .b)) (input.layout.start .b)
      else CanonicalSource.represented (input.old (input.layout.object .a)) (input.layout.start .a)+
          CanonicalSource.represented (input.old (input.layout.object .b)) (input.layout.start .b))

/-- Complete universal source execution and signed-integer correctness of
the actual fixed_add helper. Overflow is the actual returned checked status. -/
theorem fixed_add_total {F : Type} (context : Context F)
    (selected : findFunction context.program "fixed_add"=some fixed_add_ast)
    (compareSelected : findFunction context.program "magnitude_compare"=some magnitude_compare_ast)
    (canonicalSelected : findFunction context.program "canonical_sign"=some FFTRecursivePV.canonical_sign_ast)
    (before : State F) (input : Input) (well : WellScoped before)
    (rep : ∀r,WordArrayRep before (input.layout.object r) (input.layout.length (input.layout.object r)) (input.old (input.layout.object r))) :
    AddCorrect context before input := by
  obtain ⟨after,run,post,frame⟩:=fixed_add_call context selected compareSelected canonicalSelected before input well rep
  exact ⟨⟨after,run,post,frame,fun after' result second=>returned_call_unique selected compareSelected canonicalSelected run second⟩,
    rawStatus_bound input,finalData_digits input,finalData_sign_bound input,finalData_integer_correct input⟩

def recursiveContext : Context Unit:=
  {program:=FFTRecursivePV.program,foreign:=fun _ _ _ _ _=>False,
    headerConstant:=fun _=>none,builtin:=fun _ _=>none}
def fapRecursiveContext : Context Unit:=
  {program:=FapFFTRecursivePV.program,foreign:=fun _ _ _ _ _=>False,
    headerConstant:=fun _=>none,builtin:=fun _ _=>none}

/-- Source contracts are paired with independently proved syntax for each
actual preserved iterative and recursive original-profile program. Their
consumption by the complete numerical ANT pipeline remains separate. -/
theorem source_fixed_add_total (before : State Unit) (input : Input) (well : WellScoped before)
    (rep : ∀r,WordArrayRep before (input.layout.object r) (input.layout.length (input.layout.object r)) (input.old (input.layout.object r))) :
    Correspondence.SourceSyntaxCorresponds RH080Next.FFTPV.source RH080Next.FFTPV.program ∧
      AddCorrect CompareSource.sourceContext before input :=
  ⟨RH080Next.FFTPV.actual_source_syntax,fixed_add_total _ (by rfl) (by rfl) (by rfl) before input well rep⟩

theorem fap_source_fixed_add_total (before : State Unit) (input : Input) (well : WellScoped before)
    (rep : ∀r,WordArrayRep before (input.layout.object r) (input.layout.length (input.layout.object r)) (input.old (input.layout.object r))) :
    Correspondence.SourceSyntaxCorresponds RH080Next.FapFFTPV.source RH080Next.FapFFTPV.program ∧
      AddCorrect CompareSource.fapSourceContext before input :=
  ⟨RH080Next.FapFFTPV.actual_source_syntax,fixed_add_total _ (by rfl) (by rfl) (by rfl) before input well rep⟩

theorem recursive_source_fixed_add_total (before : State Unit) (input : Input) (well : WellScoped before)
    (rep : ∀r,WordArrayRep before (input.layout.object r) (input.layout.length (input.layout.object r)) (input.old (input.layout.object r))) :
    Correspondence.SourceSyntaxCorresponds FFTRecursivePV.source FFTRecursivePV.program ∧
      AddCorrect recursiveContext before input :=
  ⟨FFTRecursivePV.actual_source_syntax,fixed_add_total _ (by rfl) (by rfl) (by rfl) before input well rep⟩

theorem fap_recursive_source_fixed_add_total (before : State Unit) (input : Input) (well : WellScoped before)
    (rep : ∀r,WordArrayRep before (input.layout.object r) (input.layout.length (input.layout.object r)) (input.old (input.layout.object r))) :
    Correspondence.SourceSyntaxCorresponds FapFFTRecursivePV.source FapFFTRecursivePV.program ∧
      AddCorrect fapRecursiveContext before input :=
  ⟨FapFFTRecursivePV.actual_source_syntax,fixed_add_total _ (by rfl) (by rfl) (by rfl) before input well rep⟩

#print axioms fixed_add_total
#print axioms source_fixed_add_total
#print axioms fap_source_fixed_add_total
#print axioms recursive_source_fixed_add_total
#print axioms fap_recursive_source_fixed_add_total
end RH080Next.FFTPV.AddSource
