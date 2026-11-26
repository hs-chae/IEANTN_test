/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTRecursiveButterflyAddCoordinates
import FFTRecursiveButterflyAddWords
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
namespace RH080Next.FFTPV.RecursiveSource

/-- Exact complex sum/difference computed by the four actual source digit
algorithms, with no expected-output premise. -/
theorem four_add_pairs {total : Nat} (buffers : Buffers total)
    (start index step n half j : Nat) (shape : IndexShape start index step n total)
    (split : n=2*half) (active : j<half) (input table : Nat → Nat) (world : AddWorld (start+j)) :
    let last := addWorldFour buffers start index step n half j shape split active input table world
    ComplexSource.pair last.work 48 = FFT.IntegerModel.add
        (ComplexSource.pair world.output ((start+j)*12)) (ComplexSource.pair world.work 160) ∧
      ComplexSource.pair last.output ((start+j+half)*12) = FFT.IntegerModel.sub
        (ComplexSource.pair world.output ((start+j)*12)) (ComplexSource.pair world.work 160) := by
  dsimp only
  have coords := four_add_coordinates buffers start index step n half j shape split active input table world
  constructor
  · apply Prod.ext
    · simpa [ComplexSource.pair,FFT.IntegerModel.add,addCoordinate,expectedAddCoordinate,addComponent] using coords 0
    · simpa [ComplexSource.pair,FFT.IntegerModel.add,addCoordinate,expectedAddCoordinate,addComponent] using coords 1
  · apply Prod.ext
    · simpa [ComplexSource.pair,FFT.IntegerModel.sub,addCoordinate,expectedAddCoordinate,addComponent] using coords 2
    · simpa [ComplexSource.pair,FFT.IntegerModel.sub,addCoordinate,expectedAddCoordinate,addComponent] using coords 3

/-- Both complex outputs of the source data algorithms have genuine five
base-billion digits and one valid sign word per component. -/
theorem four_add_pairs_normalized {total : Nat} (buffers : Buffers total)
    (start index step n half j : Nat) (shape : IndexShape start index step n total)
    (split : n=2*half) (active : j<half) (input table : Nat → Nat) (world : AddWorld (start+j)) :
    let last := addWorldFour buffers start index step n half j shape split active input table world
    (∀c : Fin 2,∀k,k<5 → last.work (48+6*c.val+k)<1000000000) ∧
      (∀c : Fin 2,last.work (48+6*c.val+5)≤1) ∧ NormalizedCell last.output (start+j+half) := by
  dsimp only
  have words := four_add_words_normalized buffers start index step n half j shape split active input table world
  refine ⟨?_,?_,?_,?_⟩
  · intro c k hk
    fin_cases c
    · simpa [addWord,addComponent] using (words 0).1 k hk
    · simpa [addWord,addComponent] using (words 1).1 k hk
  · intro c
    fin_cases c
    · simpa [addWord,addComponent] using (words 0).2
    · simpa [addWord,addComponent] using (words 1).2
  · intro c k hk
    fin_cases c
    · simpa [addWord,addComponent,Nat.mul_comm] using (words 2).1 k hk
    · simpa [addWord,addComponent,Nat.mul_comm] using (words 3).1 k hk
  · intro c
    fin_cases c
    · simpa [addWord,addComponent,Nat.mul_comm] using (words 2).2
    · simpa [addWord,addComponent,Nat.mul_comm] using (words 3).2

#print axioms four_add_pairs
#print axioms four_add_pairs_normalized
end RH080Next.FFTPV.RecursiveSource
