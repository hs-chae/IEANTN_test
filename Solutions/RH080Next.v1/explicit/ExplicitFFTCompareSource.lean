/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTCompareCall
import FapFFTSource

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace RH080Next.FFTPV.CompareSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays

/-- A completed helper contract contains existence/termination, the actual
full operational Call, both untouched typed arrays, every caller allocation
framed, and correctness of every permitted execution. -/
def CompareContract {F : Type} (context : Context F) (before : State F)
    (ao al ast bo bl bst : Nat) (a b : Nat → Nat) (expected : Nat) : Prop :=
  ∃after,Call context "magnitude_compare"
    [.pointer (wordPointer ao ast),.pointer (wordPointer bo bst)] before
    (.value (.integer (integer64 expected))) after ∧
    WordArrayRep after ao al a ∧ WordArrayRep after bo bl b ∧ ReadOnlyCallerFrame before after ∧
    ∀after' result,Call context "magnitude_compare"
      [.pointer (wordPointer ao ast),.pointer (wordPointer bo bst)] before result after' →
      result=.value (.integer (integer64 expected)) ∧ after'=after

/-- Universal actual C helper execution, including same-object and overlapping
slice inputs. No input word is written and no separation premise is needed. -/
theorem magnitude_compare_total {F : Type} (context : Context F)
    (selected : findFunction context.program "magnitude_compare"=some magnitude_compare_ast)
    (before : State F) (ao al ast bo bl bst : Nat) (a b : Nat → Nat)
    (well : SourceLocals.WellScoped before)
    (left : WordArrayRep before ao al a) (right : WordArrayRep before bo bl b)
    (leftBound : ast+5≤al) (rightBound : bst+5≤bl) :
    CompareContract context before ao al ast bo bl bst a b
      (FFT.Limbs.compareDigits (fun i=>a (ast+i)) (fun i=>b (bst+i)) 5) := by
  obtain ⟨after,run,postLeft,postRight,frame⟩ :=
    magnitude_compare_call context selected before ao al ast bo bl bst a b well left right leftBound rightBound
  exact ⟨after,run,postLeft,postRight,frame,fun after' result second => returned_call_unique selected run second⟩

/-- The source helper compares the actual encoded base-billion integers.
This explicitly consumes the independent mathematical carry/positional-value
proof instead of stopping at an equality with a program-shaped recurrence. -/
theorem magnitude_compare_value_total {F : Type} (context : Context F)
    (selected : findFunction context.program "magnitude_compare"=some magnitude_compare_ast)
    (before : State F) (ao al ast bo bl bst : Nat) (a b : Nat → Nat)
    (well : SourceLocals.WellScoped before)
    (left : WordArrayRep before ao al a) (right : WordArrayRep before bo bl b)
    (leftBound : ast+5≤al) (rightBound : bst+5≤bl)
    (digitsA : ∀i<5,a (ast+i)<1000000000) (digitsB : ∀i<5,b (bst+i)<1000000000) :
    CompareContract context before ao al ast bo bl bst a b
      (if FFT.Limbs.magnitude 1000000000 5 (fun i=>b (bst+i))<FFT.Limbs.magnitude 1000000000 5 (fun i=>a (ast+i)) then 2
        else if FFT.Limbs.magnitude 1000000000 5 (fun i=>a (ast+i))<FFT.Limbs.magnitude 1000000000 5 (fun i=>b (bst+i)) then 0 else 1) := by
  have correct := FFT.Limbs.compareDigits_correct 1000000000 5 (by norm_num)
    (fun i=>a (ast+i)) (fun i=>b (bst+i)) digitsA digitsB
  have total := magnitude_compare_total context selected before ao al ast bo bl bst a b well left right leftBound rightBound
  rwa [correct] at total

def sourceContext : Context Unit :=
  {program:=RH080Next.FFTPV.program,foreign:=fun _ _ _ _ _=>False,
    headerConstant:=fun _=>none,builtin:=fun _ _=>none}

def fapSourceContext : Context Unit :=
  {program:=RH080Next.FapFFTPV.program,foreign:=fun _ _ _ _ _=>False,
    headerConstant:=fun _=>none,builtin:=fun _ _=>none}

/-- Actual w4 C file's independently proved syntax is paired with its complete
mathematical helper contract. This does not assert that the whole FFT program
or its numerical norm output is already verified. -/
theorem source_magnitude_compare_total (before : State Unit)
    (ao al ast bo bl bst : Nat) (a b : Nat → Nat) (well : SourceLocals.WellScoped before)
    (left : WordArrayRep before ao al a) (right : WordArrayRep before bo bl b)
    (leftBound : ast+5≤al) (rightBound : bst+5≤bl)
    (digitsA : ∀i<5,a (ast+i)<1000000000) (digitsB : ∀i<5,b (bst+i)<1000000000) :
    Correspondence.SourceSyntaxCorresponds RH080Next.FFTPV.source RH080Next.FFTPV.program ∧
    CompareContract sourceContext before ao al ast bo bl bst a b
      (if FFT.Limbs.magnitude 1000000000 5 (fun i=>b (bst+i))<FFT.Limbs.magnitude 1000000000 5 (fun i=>a (ast+i)) then 2
        else if FFT.Limbs.magnitude 1000000000 5 (fun i=>a (ast+i))<FFT.Limbs.magnitude 1000000000 5 (fun i=>b (bst+i)) then 0 else 1) :=
  ⟨RH080Next.FFTPV.actual_source_syntax,
    magnitude_compare_value_total sourceContext (by rfl) before ao al ast bo bl bst a b well left right leftBound rightBound digitsA digitsB⟩

/-- The distinct original Fap C source has the same checked helper body and
its own independent source-syntax proof. The actual source file is preserved. -/
theorem fap_source_magnitude_compare_total (before : State Unit)
    (ao al ast bo bl bst : Nat) (a b : Nat → Nat) (well : SourceLocals.WellScoped before)
    (left : WordArrayRep before ao al a) (right : WordArrayRep before bo bl b)
    (leftBound : ast+5≤al) (rightBound : bst+5≤bl)
    (digitsA : ∀i<5,a (ast+i)<1000000000) (digitsB : ∀i<5,b (bst+i)<1000000000) :
    Correspondence.SourceSyntaxCorresponds RH080Next.FapFFTPV.source RH080Next.FapFFTPV.program ∧
    CompareContract fapSourceContext before ao al ast bo bl bst a b
      (if FFT.Limbs.magnitude 1000000000 5 (fun i=>b (bst+i))<FFT.Limbs.magnitude 1000000000 5 (fun i=>a (ast+i)) then 2
        else if FFT.Limbs.magnitude 1000000000 5 (fun i=>a (ast+i))<FFT.Limbs.magnitude 1000000000 5 (fun i=>b (bst+i)) then 0 else 1) :=
  ⟨RH080Next.FapFFTPV.actual_source_syntax,
    magnitude_compare_value_total fapSourceContext (by rfl) before ao al ast bo bl bst a b well left right leftBound rightBound digitsA digitsB⟩

#print axioms magnitude_compare_total
#print axioms magnitude_compare_value_total
#print axioms source_magnitude_compare_total
#print axioms fap_source_magnitude_compare_total
end RH080Next.FFTPV.CompareSource
