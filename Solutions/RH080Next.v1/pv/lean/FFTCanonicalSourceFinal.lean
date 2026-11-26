/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTCanonicalCall
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.CanonicalSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays

def CanonicalContract {F : Type} (context : Context F) (before : State F)
    (object size start : Nat) (old : Nat → Nat) : Prop :=
  ∃after, Call context "canonical_sign" [.pointer (wordPointer object start)] before
      (.value (.integer (integer64 0))) after ∧
    WordArrayRep after object size (canonicalData old start) ∧ CopyLoop.CallerFrame before after object ∧
    ∀after' result, Call context "canonical_sign" [.pointer (wordPointer object start)] before result after' →
      result = .value (.integer (integer64 0)) ∧ after' = after

theorem canonical_sign_total {F : Type} (context : Context F)
    (selected : findFunction context.program "canonical_sign" = some FFTRecursivePV.canonical_sign_ast)
    (before : State F) (object size start : Nat) (old : Nat → Nat)
    (well : SourceLocals.WellScoped before) (rep : WordArrayRep before object size old) (bound : start+6 ≤ size)
    (digits : ∀i, i < 5 → old (start+i) < 1000000000) : CanonicalContract context before object size start old := by
  obtain ⟨after, run, output, frame⟩ := canonical_sign_call context selected before object size start old well rep bound digits
  exact ⟨after, run, output, frame, fun after' result second => returned_call_unique selected run second⟩

/-- The true base-billion signed integer represented by the actual six words. -/
def represented (old : Nat → Nat) (start : Nat) : Int :=
  FFT.Limbs.signed (decide (old (start+5) ≠ 0))
    (FFT.Limbs.magnitude 1000000000 5 (fun i => old (start+i)))

/-- Source canonicalization preserves the actual represented signed integer,
consuming the independent positional-value/canonical-sign theorem. -/
theorem canonicalData_preserves (old : Nat → Nat) (start : Nat) :
    represented (canonicalData old start) start = represented old start := by
  have magnitudeEq : FFT.Limbs.magnitude 1000000000 5 (fun i => canonicalData old start (start+i)) =
      FFT.Limbs.magnitude 1000000000 5 (fun i => old (start+i)) := by
    unfold FFT.Limbs.magnitude
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only
    rw [canonicalData_digit old start i (Finset.mem_range.mp hi)]
  have signEq : decide (canonicalData old start (start+5) ≠ 0) =
      if digitSum old start 5 = 0 then false else decide (old (start+5) ≠ 0) := by
    by_cases hz : digitSum old start 5 = 0 <;> simp [canonicalData_sign, hz]
  unfold represented
  rw [magnitudeEq, signEq]
  exact FFT.Limbs.canonical_sign_preserves 1000000000 5 (by norm_num)
    (fun i => old (start+i)) (decide (old (start+5) ≠ 0))

/-- Independent source syntax, total operational correctness, and preservation
of the mathematical signed integer. This verifies one actual helper only. -/
theorem source_canonical_sign_total (before : State Unit) (object size start : Nat) (old : Nat → Nat)
    (well : SourceLocals.WellScoped before) (rep : WordArrayRep before object size old) (bound : start+6 ≤ size)
    (digits : ∀i, i < 5 → old (start+i) < 1000000000) :
    Correspondence.SourceSyntaxCorresponds FFTRecursivePV.source FFTRecursivePV.program ∧
      CanonicalContract CopyLoop.sourceContext before object size start old ∧
      represented (canonicalData old start) start = represented old start :=
  ⟨FFTRecursivePV.actual_source_syntax,
    canonical_sign_total _ (by rfl) before object size start old well rep bound digits,
    canonicalData_preserves old start⟩

#print axioms canonical_sign_total
#print axioms canonicalData_preserves
#print axioms source_canonical_sign_total
end RH080Next.FFTPV.CanonicalSource
