/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTInputLoaderDecoded
import ExplicitFFTInputLoaderView
import FFTPairedIntModel
import W4FFTPairedIntModel
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.InputLoader
open GoldbachDirect

theorem pair_congr_words (a b : Nat → Nat) (start target : Nat)
    (same : ∀r<12,a (start+r)=b (target+r)) : ComplexSource.pair a start=ComplexSource.pair b target:=by
  apply Prod.ext
  · exact ComplexSource.represented_congr a b start target (fun r hr=> same r (by omega))
  · apply ComplexSource.represented_congr a b (start+6) (target+6)
    intro r hr
    simpa only [Nat.add_assoc] using same (6+r) (by omega)

def Profile.mathematicalInput (p : Profile) (k : Nat) : Int×Int:=
  match p with
  | .fap=> FFT.IntegerModel.input p.grid k
  | .w4=> FFT.IntegerModel.W4.input p.grid k

theorem fap_coefficient (j : Nat) : FFT.IntegerModel.coefficient j=
    (RH080Next.FapPV.Data.encodedNode j:Int)-(InputCell.scale:Int):=by
  simp [FFT.IntegerModel.coefficient,FFT.IntegerModel.encoded,RH080Next.FapPV.Data.encodedNode,RH080Next.FapPV.Data.scale,InputCell.scale]

theorem mathematicalInput_formula (p : Profile) (k : Nat) : p.mathematicalInput k=
    if k< p.count then (((p.encoded k:Int)-(InputCell.scale:Int))*100000000000000000000,0)
    else if p.grid-k< p.count then (((p.encoded (p.grid-k):Int)-(InputCell.scale:Int))*100000000000000000000,0) else (0,0):=by
  cases p with
  | fap=>
    by_cases forward : k<400
    · simp [Profile.mathematicalInput,Profile.grid,Profile.count,Profile.encoded,FFT.IntegerModel.input,forward,fap_coefficient] <;> rfl
    · simp [Profile.mathematicalInput,Profile.grid,Profile.count,Profile.encoded,FFT.IntegerModel.input,forward,fap_coefficient] <;> rfl
  | w4=>
    by_cases forward : k<2520
    · simp [Profile.mathematicalInput,Profile.grid,Profile.count,Profile.encoded,FFT.IntegerModel.W4.input,
        FFT.IntegerModel.sparseInput,FFT.IntegerModel.W4.coefficient,InputCell.scale,forward] <;> rfl
    · simp [Profile.mathematicalInput,Profile.grid,Profile.count,Profile.encoded,FFT.IntegerModel.W4.input,
        FFT.IntegerModel.sparseInput,FFT.IntegerModel.W4.coefficient,InputCell.scale,forward] <;> rfl

/-- The actual word model at loop completion represents precisely the existing
original Fap/w4 integer FFT input, at every one of the original grid positions. -/
theorem completed_input_pair (p : Profile) (k : Nat) (hk : k< p.grid) :
    ComplexSource.pair (currentData p.encoded p.grid p.count) (12*k)=p.mathematicalInput k:=by
  have shape:=p.shape
  rw [mathematicalInput_formula]
  by_cases forward : k< p.count
  · rw [if_pos forward]
    have same : ∀r<12,currentData p.encoded p.grid p.count (12*k+r)=InputCell.cell (p.encoded k) (0+r):=by
      intro r hr
      simpa only [if_pos forward,Nat.zero_add] using currentData_decoded p.encoded p.grid p.count k r shape.2.1 hk hr
    exact (pair_congr_words _ _ (12*k) 0 same).trans (InputCell.pair_value (p.encoded k))
  · rw [if_neg forward]
    by_cases mirror : p.grid-k< p.count
    · rw [if_pos mirror]
      have same : ∀r<12,currentData p.encoded p.grid p.count (12*k+r)=InputCell.cell (p.encoded (p.grid-k)) (0+r):=by
        intro r hr
        simpa only [if_neg forward,if_pos mirror,Nat.zero_add] using currentData_decoded p.encoded p.grid p.count k r shape.2.1 hk hr
      exact (pair_congr_words _ _ (12*k) 0 same).trans (InputCell.pair_value (p.encoded (p.grid-k)))
    · rw [if_neg mirror]
      have same : ∀r<12,currentData p.encoded p.grid p.count (12*k+r)=(fun _ : Nat=>0) (0+r):=by
        intro r hr
        simpa only [if_neg forward,if_neg mirror] using currentData_decoded p.encoded p.grid p.count k r shape.2.1 hk hr
      rw [pair_congr_words _ (fun _=>0) (12*k) 0 same]
      simp [ComplexSource.pair,CanonicalSource.represented,FFT.Limbs.signed,FFT.Limbs.magnitude]

#print axioms fap_coefficient
#print axioms completed_input_pair
end RH080Next.FFTPV.InputLoader
