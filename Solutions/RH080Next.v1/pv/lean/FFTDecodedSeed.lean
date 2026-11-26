/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTVerifiedRoot
import FFTSeedBounds
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.Certified
open GoldbachDirect GoldbachDirect.Semantics
noncomputable section

def decodeMagnitude (words : List Nat) (start : Nat) : ℝ :=
  ((words.getD start 0 : ℝ)+1000000000*(words.getD (start+1) 0 : ℝ)+
    1000000000000000000*(words.getD (start+2) 0 : ℝ)+
    1000000000000000000000000000*(words.getD (start+3) 0 : ℝ)+
    1000000000000000000000000000000000000*(words.getD (start+4) 0 : ℝ))/
      1000000000000000000000000000000000000

def decodeRootWords (words : List Nat) : ℂ :=
  ⟨if words.getD 5 0=0 then decodeMagnitude words 0 else -decodeMagnitude words 0,
   if words.getD 11 0=0 then decodeMagnitude words 6 else -decodeMagnitude words 6⟩

theorem decoded_actual_seed : decodeRootWords expectedRootWords=RH080Next.FFT.rootSeed := by
  apply Complex.ext <;> norm_num [decodeRootWords,decodeMagnitude,expectedRootWords,RH080Next.FFT.rootSeed]

/-- A source-linked selected C execution with a true complex-root enclosure.
Caller framing and all-permitted-order refinement remain separate obligations. -/
theorem source_initializer_seed_bound :
    GoldbachDirect.Correspondence.SourceSyntaxCorresponds FFTPV.source FFTPV.program ∧
    ∃status : Integer,∃after : State Unit,∃words : List Nat,
      Call context "initialize_root" rootArgs rawScratch (.value (.integer status)) after ∧
      status.bits=0 ∧readRoot after=some words ∧
      ‖decodeRootWords words-RH080Next.FFT.negativeRoot 16777216‖≤
        (1/100000000000000000000000000 : ℝ) := by
  obtain ⟨hsyntax,status,after,run,zero,words⟩ := source_linked_root_execution
  refine ⟨hsyntax,status,after,expectedRootWords,run,zero,words,?_⟩
  rw [decoded_actual_seed]
  exact RH080Next.FFT.rootSeed_error

#print axioms decoded_actual_seed
#print axioms source_initializer_seed_bound
end
end RH080Next.FFTPV.Certified
