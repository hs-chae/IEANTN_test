/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTActualRoot
import FFTSource
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.Certified
open GoldbachDirect GoldbachDirect.Semantics

def expectedRootWords : List Nat :=
  [239728737,242879801,999929872,999999999,0,0,
    169179084,384123903,507028292,374,0,1]

/-- An actual full C-semantics Call and its exact observed words, extracted from
closed certifying execution, with no application result or foreign oracle.
This states one permitted evaluation order in the specified canonical frame. -/
theorem actual_root_execution : ∃status : Integer,∃after : State Unit,
    Call context "initialize_root" rootArgs rawScratch (.value (.integer status)) after ∧
      status.bits=0 ∧readRoot after=some expectedRootWords := by
  have h := actual_root_result
  change rootResult=some (0::expectedRootWords) at h
  cases hr : invokeRoot with
  | none => simp [rootResult,hr] at h
  | some out =>
    cases ht : out.val.1 with
    | terminated exit => simp [rootResult,hr,ht] at h
    | value result =>
      cases result with
      | pointer p => simp [rootResult,hr,ht] at h
      | null => simp [rootResult,hr,ht] at h
      | string text => simp [rootResult,hr,ht] at h
      | unit => simp [rootResult,hr,ht] at h
      | integer status =>
        cases hs : readRoot out.val.2 with
        | none => simp [rootResult,hr,ht,hs] at h
        | some words =>
          have he : status.bits::words=0::expectedRootWords := by
            simpa [rootResult,hr,ht,hs] using h
          have hd := List.cons.inj he
          refine ⟨status,out.val.2,?_,hd.1,?_⟩
          · simpa only [ht] using invokeRoot_sound hr
          · rw [hs,hd.2]

theorem source_linked_root_execution :
    GoldbachDirect.Correspondence.SourceSyntaxCorresponds FFTPV.source FFTPV.program ∧
    ∃status : Integer,∃after : State Unit,
      Call context "initialize_root" rootArgs rawScratch (.value (.integer status)) after ∧
        status.bits=0 ∧readRoot after=some expectedRootWords :=
  ⟨FFTPV.actual_source_syntax,actual_root_execution⟩

#print axioms actual_root_execution
#print axioms source_linked_root_execution
end RH080Next.FFTPV.Certified
