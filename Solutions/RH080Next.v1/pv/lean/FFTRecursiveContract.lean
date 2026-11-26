/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTRecursiveHeaderTotal
import FFTRecursiveMergeTrace
import FFTRecursiveCallAssembly
import FFTRecursiveLeafTotal
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
namespace RH080Next.FFTPV.RecursiveSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceBindings ApplicationBirthFrame

theorem array_words_unique {F : Type} {state : State F} {object size : Nat} {a b : Nat → Nat}
    (ha : WordArrayRep state object size a) (hb : WordArrayRep state object size b) :
    ∀k,k<size → a k=b k := by
  intro k hk
  simpa [integer64] using (word_load ha hk).symm.trans (word_load hb hk)

/-- The full mathematical and physical contract of one true recursive Call.
Only actual represented words, not arbitrary values outside their allocation,
are part of the physical preservation claim. -/
structure CallPost {F : Type} {total : Nat} (buffers : Buffers total)
    (s start index step : Nat) (input table oldOutput oldWork : Nat → Nat)
    (before after : State F) (output work : Nat → Nat) : Prop where
  arrays : ∀r,WordArrayRep after (buffers.object r) (buffers.length r) (bufferData input table output work r)
  frame : MultiplyCall.CallerFrame before after [buffers.object .output,buffers.object .work]
  trace : FFT.IntegerModel.ExecutionTrace (stages table total) (cell input) s index step (cells output start (2^s))
  normalized : ∀k,k<2^s → NormalizedCell output (start+k)
  outputOutside : ∀k,k<buffers.length .output → (k<start*12 ∨ (start+2^s)*12≤k) → output k=oldOutput k
  workOutside : ∀k,k<buffers.length .work → 60≤k → (k<160 ∨ 172≤k) → work k=oldWork k

/-- Changing only the naming functions of an identical physical host-array
representation preserves the mathematical trace and every physical frame. -/
theorem CallPost.represent {F : Type} {total : Nat} {buffers : Buffers total}
    {s start index step : Nat} {input table oldOutput oldWork output work output' work' : Nat → Nat}
    {before after : State F} (h : CallPost buffers s start index step input table oldOutput oldWork before after output work)
    (shape : IndexShape start index step (2^s) total)
    (arrays : ∀r,WordArrayRep after (buffers.object r) (buffers.length r) (bufferData input table output' work' r)) :
    CallPost buffers s start index step input table oldOutput oldWork before after output' work' := by
  have outEq:=array_words_unique (arrays .output) (h.arrays .output)
  have workEq:=array_words_unique (arrays .work) (h.arrays .work)
  have cellWords : ∀k,k<2^s → ∀d,d<12 → output' (12*(start+k)+d)=output (12*(start+k)+d) := by
    intro k hk d hd
    apply outEq
    have bound:=buffers.outputBound
    have within:=shape.output
    omega
  have cellsEq : cells output' start (2^s)=cells output start (2^s) :=
    cells_congr (fun k hk=>cell_congr (cellWords k hk))
  refine ⟨arrays,h.frame,?_,?_,?_,?_⟩
  · rw [cellsEq];exact h.trace
  · intro k hk;exact normalized_congr (cellWords k hk) (h.normalized k hk)
  · intro k hk outside;exact (outEq k hk).trans (h.outputOutside k hk outside)
  · intro k hk lo hi;exact (workEq k hk).trans (h.workOutside k hk lo hi)

/-- A terminating actual Call, correctness of its words and uniqueness of
EVERY permitted source Call, including terminated alternatives. -/
def StrongContract {F : Type} (context : Context F) {total : Nat} (buffers : Buffers total)
    (input table : Nat → Nat) (s start index step : Nat) : Prop :=
  ∀(before : State F) (output work : Nat → Nat),WellScoped before →
    (∀r,WordArrayRep before (buffers.object r) (buffers.length r) (bufferData input table output work r)) →
    ∃after output' work',Call context "fft_recursive"
        (arguments (buffers.object .output) (buffers.object .input) (buffers.object .twiddle)
          (buffers.object .work) start index step (2^s) total) before (.value (.integer (integer64 0))) after ∧
      CallPost buffers s start index step input table output work before after output' work' ∧
      ∀other result,Call context "fft_recursive"
        (arguments (buffers.object .output) (buffers.object .input) (buffers.object .twiddle)
          (buffers.object .work) start index step (2^s) total) before result other →
        result=.value (.integer (integer64 0)) ∧ other=after

theorem StrongContract.child {F : Type} {context : Context F} {total : Nat} {buffers : Buffers total}
    {input table : Nat → Nat} {s start index step : Nat}
    (h : StrongContract context buffers input table s start index step) :
    Header.ChildContract context buffers start index step (2^s) input table := by
  intro before output work well arrays
  obtain ⟨after,newOutput,newWork,called,post,every⟩:=h before output work well arrays
  exact ⟨after,newOutput,newWork,called,post.arrays,post.frame,every⟩

/-- Recover the stronger induction facts at the actual child Calls exposed by
the source header, even when its representation functions use different names. -/
theorem StrongContract.at_call {F : Type} {context : Context F} {total : Nat} {buffers : Buffers total}
    {input table output work output' work' : Nat → Nat} {s start index step : Nat} {before after : State F}
    (h : StrongContract context buffers input table s start index step)
    (shape : IndexShape start index step (2^s) total)
    (well : WellScoped before)
    (arrays : ∀r,WordArrayRep before (buffers.object r) (buffers.length r) (bufferData input table output work r))
    (called : Call context "fft_recursive"
      (arguments (buffers.object .output) (buffers.object .input) (buffers.object .twiddle)
        (buffers.object .work) start index step (2^s) total) before (.value (.integer (integer64 0))) after)
    (newArrays : ∀r,WordArrayRep after (buffers.object r) (buffers.length r) (bufferData input table output' work' r)) :
    CallPost buffers s start index step input table output work before after output' work' := by
  obtain ⟨chosen,newOutput,newWork,chosenCall,post,every⟩:=h before output work well arrays
  obtain ⟨_,rfl⟩:=every _ _ called
  exact post.represent shape newArrays

#print axioms CallPost.represent
#print axioms StrongContract.at_call
end RH080Next.FFTPV.RecursiveSource
