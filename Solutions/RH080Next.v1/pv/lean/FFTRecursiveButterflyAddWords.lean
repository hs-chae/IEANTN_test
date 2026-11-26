/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTRecursiveButterflyAddWorld
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
noncomputable section
namespace RH080Next.FFTPV.RecursiveSource

def addWord {left : Nat} (world : AddWorld left) (right : Nat) (i : Fin 4) (k : Nat) : Nat :=
  if i.val<2 then world.work (48+6*(addComponent i).val+k)
  else world.output (right*12+6*(addComponent i).val+k)

def AddWordNormalized {left : Nat} (world : AddWorld left) (right : Nat) (i : Fin 4) : Prop :=
  (∀k,k<5 → addWord world right i k<1000000000) ∧ addWord world right i 5≤1

theorem add_word_self_normalized {total : Nat} (buffers : Buffers total)
    (start index step n half j : Nat) (shape : IndexShape start index step n total)
    (split : n=2*half) (active : j<half) (input table : Nat → Nat)
    (i : Fin 4) (world : AddWorld (start+j)) :
    AddWordNormalized (addWorldAdvance buffers start index step n half j shape split active input table i world)
      (start+j+half) i := by
  let p := addWorldInput buffers start index step n half j shape split active input table i world
  have digits := AddSource.finalData_digits p
  have sign := AddSource.finalData_sign_bound p
  by_cases hi : i.val<2
  · simpa [AddWordNormalized,addWord,addWorldAdvance,addOutputData,addWorkData,
      p,addWorldInput,butterflyAddInput,butterflyAddLayout,IncrementSource.base,hi] using And.intro digits sign
  · simpa [AddWordNormalized,addWord,addWorldAdvance,addOutputData,addWorkData,
      p,addWorldInput,butterflyAddInput,butterflyAddLayout,IncrementSource.base,hi] using And.intro digits sign

theorem add_word_other {total : Nat} (buffers : Buffers total)
    (start index step n half j : Nat) (shape : IndexShape start index step n total)
    (split : n=2*half) (active : j<half) (input table : Nat → Nat)
    (i target : Fin 4) (world : AddWorld (start+j)) (different : i≠target) (k : Nat) (hk : k<6) :
    addWord (addWorldAdvance buffers start index step n half j shape split active input table i world)
      (start+j+half) target k = addWord world (start+j+half) target k := by
  let p := addWorldInput buffers start index step n half j shape split active input table i world
  have ni := i.isLt
  have nt := target.isLt
  have ne : i.val≠target.val := by intro same;exact different (Fin.ext same)
  by_cases hi : i.val<2
  · by_cases ht : target.val<2
    · have position : p.layout.start .out=48+6*(addComponent i).val := by
        simp [p,addWorldInput,butterflyAddInput,butterflyAddLayout,hi]
      have disjoint : 48+6*(addComponent target).val+k < p.layout.start .out ∨
          p.layout.start .out+6 ≤ 48+6*(addComponent target).val+k := by
        rw [position]
        simp only [addComponent]
        omega
      have actual := AddSource.finalData_outside p (48+6*(addComponent target).val+k) disjoint
      simpa [addWord,addWorldAdvance,addWorkData,p,addWorldInput,butterflyAddInput,butterflyAddLayout,bufferData,hi,ht] using actual
    · simp [addWord,ht,addWorldAdvance,addOutputData,hi]
  · by_cases ht : target.val<2
    · simp [addWord,ht,addWorldAdvance,addWorkData,hi]
    · have position : p.layout.start .out=(start+j+half)*12+6*(addComponent i).val := by
        simp [p,addWorldInput,butterflyAddInput,butterflyAddLayout,hi]
      have disjoint : (start+j+half)*12+6*(addComponent target).val+k < p.layout.start .out ∨
          p.layout.start .out+6 ≤ (start+j+half)*12+6*(addComponent target).val+k := by
        rw [position]
        simp only [addComponent]
        omega
      have actual := AddSource.finalData_outside p ((start+j+half)*12+6*(addComponent target).val+k) disjoint
      simpa [addWord,addWorldAdvance,addOutputData,p,addWorldInput,butterflyAddInput,butterflyAddLayout,bufferData,hi,ht] using actual

theorem add_word_other_normalized {total : Nat} (buffers : Buffers total)
    (start index step n half j : Nat) (shape : IndexShape start index step n total)
    (split : n=2*half) (active : j<half) (input table : Nat → Nat)
    (i target : Fin 4) (world : AddWorld (start+j)) (different : i≠target)
    (old : AddWordNormalized world (start+j+half) target) :
    AddWordNormalized (addWorldAdvance buffers start index step n half j shape split active input table i world)
      (start+j+half) target := by
  constructor
  · intro k hk
    rw [add_word_other buffers start index step n half j shape split active input table i target world different k (by omega)]
    exact old.1 k hk
  · rw [add_word_other buffers start index step n half j shape split active input table i target world different 5 (by norm_num)]
    exact old.2

/-- Every scalar produced by the actual four source algorithms is normalized;
the previous three results are retained by proved six-word disjointness. -/
theorem four_add_words_normalized {total : Nat} (buffers : Buffers total)
    (start index step n half j : Nat) (shape : IndexShape start index step n total)
    (split : n=2*half) (active : j<half) (input table : Nat → Nat) (world : AddWorld (start+j)) :
    ∀i : Fin 4, AddWordNormalized (addWorldFour buffers start index step n half j shape split active input table world)
      (start+j+half) i := by
  let next := fun i => addWorldAdvance buffers start index step n half j shape split active input table i
  have make := add_word_self_normalized buffers start index step n half j shape split active input table
  have keep := add_word_other_normalized buffers start index step n half j shape split active input table
  intro i
  change AddWordNormalized (next 3 (next 2 (next 1 (next 0 world)))) (start+j+half) i
  fin_cases i
  · exact keep 3 0 _ (by decide) (keep 2 0 _ (by decide) (keep 1 0 _ (by decide) (make 0 world)))
  · exact keep 3 1 _ (by decide) (keep 2 1 _ (by decide) (make 1 (next 0 world)))
  · exact keep 3 2 _ (by decide) (make 2 (next 1 (next 0 world)))
  · exact make 3 (next 2 (next 1 (next 0 world)))

#print axioms four_add_words_normalized
end RH080Next.FFTPV.RecursiveSource
