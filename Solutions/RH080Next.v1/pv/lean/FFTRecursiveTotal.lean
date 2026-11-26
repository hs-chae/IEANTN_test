/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTRecursiveNonleaf
import FFTIntermediateBounds
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
noncomputable section
namespace RH080Next.FFTPV.RecursiveSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceBindings

/-- Exact physical global-table entry selected at a positive recursive level. -/
theorem stage_getD (table : Nat → Nat) (total s k : Nat) (hk : k<2^s) :
    (stages table total (s+1)).getD k (0,0)=cell table (k*(total/2^(s+1))) := by
  simp [stages,hk]

/-- Complete source recursive FFT correctness, with actual Call existence and
EVERY Call. Every primitive domain is derived from independent integer traces,
the global input mass and global twiddle errors; no successful C output is a
premise. Full allocation/slice/work words and caller lifetimes are preserved. -/
theorem recursive_strong_total {F : Type} (context : Context F) (helpers : Helpers context)
    {total : Nat} (buffers : Buffers total) (input table : Nat → Nat) (S : Nat)
    (totalPower : total=2^S) (stageLimit : S≤24)
    (inputNormalized : ∀k,k<total → NormalizedCell input k)
    (tableNormalized : ∀k,k<total/2 → NormalizedCell table k)
    (mass : FFT.coefficientMass (2^S) (fun j=>FFT.IntegerModel.decode (cell input j))≤362)
    (twiddleError : ∀t,t<S → ∀j,j<2^t →
      ‖FFT.IntegerModel.decode ((stages table total (t+1)).getD j (0,0))-FFT.negativeRoot (2*2^t)^j‖≤
        (1/10000000000000000000:ℝ))
    (s start index step : Nat) (depth : s≤S)
    (shape : IndexShape start index step (2^s) total) :
    StrongContract context buffers input table s start index step := by
  induction s generalizing start index step with
  | zero => exact leaf_strong_contract context helpers.recursive helpers.copy buffers input table start index step shape inputNormalized
  | succ s ih =>
    have split : 2^(s+1)=2*2^s := by rw [Nat.pow_succ];omega
    have positive : 0<2^s := by positivity
    have childShapes:=shape.children split positive
    apply nonleaf_strong_contract context helpers buffers input table s start index step shape
      (ih start index (step*2) (by omega) childShapes.1)
      (ih (start+2^s) (index+step) (step*2) (by omega) childShapes.2)
    · intro a i d out childShape trace k hk
      apply trace.subtransform_norm_le (by omega) stageLimit childShape.index
        (by rw [←totalPower];exact childShape.stride) mass twiddleError k hk
    · intro r hr
      apply tableNormalized
      rw [shape.stride_exact]
      have halfTotal : total/2=step*2^s := by
        have identity : total=2*(step*2^s) := by
          rw [←shape.stride,split]
          ring
        rw [identity,Nat.mul_div_right] <;> omega
      rw [halfTotal]
      have stepPositive:=shape.step_positive
      nlinarith
    · intro r hr
      have bound:=FFT.IntegerModel.stage_norm_le_two (stages table total) s r
        (twiddleError s (by omega) r hr)
      rw [stage_getD table total s r hr] at bound
      exact bound

/-- Literal source/syntax association and the complete recursive Call theorem
for the unchanged n=2^17/2^24-compatible source program. This is the recursion
component; main allocation/input/table/output and ANT composition are separate. -/
theorem source_recursive_total
    {total : Nat} (buffers : Buffers total) (input table : Nat → Nat) (S : Nat)
    (totalPower : total=2^S) (stageLimit : S≤24)
    (inputNormalized : ∀k,k<total → NormalizedCell input k)
    (tableNormalized : ∀k,k<total/2 → NormalizedCell table k)
    (mass : FFT.coefficientMass (2^S) (fun j=>FFT.IntegerModel.decode (cell input j))≤362)
    (twiddleError : ∀t,t<S → ∀j,j<2^t →
      ‖FFT.IntegerModel.decode ((stages table total (t+1)).getD j (0,0))-FFT.negativeRoot (2*2^t)^j‖≤
        (1/10000000000000000000:ℝ))
    (s start index step : Nat) (depth : s≤S)
    (shape : IndexShape start index step (2^s) total) :
    Correspondence.SourceSyntaxCorresponds FFTRecursivePV.source FFTRecursivePV.program ∧
    StrongContract CopyLoop.sourceContext buffers input table s start index step :=
  ⟨FFTRecursivePV.actual_source_syntax,recursive_strong_total CopyLoop.sourceContext actual_helpers buffers input table S
    totalPower stageLimit inputNormalized tableNormalized mass twiddleError s start index step depth shape⟩

#print axioms recursive_strong_total
#print axioms source_recursive_total
end RH080Next.FFTPV.RecursiveSource
