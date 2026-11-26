/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTSourceSteps
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.WordArrays
open GoldbachDirect

/-- Actual primitive memory operations of the initialization loop. This is a
memory subtrace, not a claim that the complete C function has executed. -/
inductive ZeroStoreTrace {F : Type} (object length : Nat) : Nat → State F → State F → Prop
  | done (state : State F) : ZeroStoreTrace object length length state state
  | step {j : Nat} {before middle after : State F} (active : j<length)
      (written : before.store (wordPointer object j) (.integer (integer64 0))=some middle)
      (rest : ZeroStoreTrace object length (j+1) middle after) :
      ZeroStoreTrace object length j before after

theorem zero_trace_exists {F : Type} (steps filled object length : Nat) (state : State F)
    (remaining : filled+steps=length) (mode : state.mode=.host)
    (present : state.objects object=some (zeroPrefixObject length filled)) :
    ∃ after, ZeroStoreTrace object length filled state after ∧after.mode=.host ∧
      after.objects object=some (zeroPrefixObject length length) ∧
      ∀key,key≠object→after.objects key=state.objects key := by
  induction steps generalizing filled state with
  | zero =>
    have he : filled=length := by omega
    subst filled
    exact ⟨state,.done state,mode,present,fun _ _=>rfl⟩
  | succ steps ih =>
    have hp : filled<length := by omega
    let middle : State F := {state with objects := fun key => if key=object then some (zeroPrefixObject length (filled+1)) else state.objects key}
    have hm : middle.mode=.host := mode
    have ho : middle.objects object=some (zeroPrefixObject length (filled+1)) := by simp [middle]
    obtain ⟨after,trace,host,done,outside⟩ := ih (filled+1) middle (by omega) hm ho
    refine ⟨after,.step hp (zeroPrefix_store mode present hp) trace,host,done,?_⟩
    intro key different
    rw [outside key different]
    simp [middle,different]

/-- Caller-independent successful calloc is still a byte allocation. The
application's subsequent u64 store subtrace, not calloc itself, establishes the
word representation. -/
theorem calloc_prefix_zero {F : Type} {before after : State F} {pointer : Pointer} {length : Nat}
    (host : before.mode=.host)
    (born : before.allocate .host (8*length) (PlatformMemory.zeroBytes (8*length))=
      some (pointer,after)) :
    after.mode=.host ∧after.objects pointer.object=some (zeroPrefixObject length 0) := by
  unfold State.allocate at born
  split_ifs at born with occupied
  cases Option.some.inj born
  simp [host,zeroPrefix_zero]

/-- Complete mathematical memory-initialization obligation for every finite
buffer size, derived from byte birth and the actual typed store operation. -/
theorem calloc_to_zero_words {F : Type} {before after : State F} {pointer : Pointer} {length : Nat}
    (host : before.mode=.host)
    (born : before.allocate .host (8*length) (PlatformMemory.zeroBytes (8*length))=
      some (pointer,after)) :
    ∃ initialized,ZeroStoreTrace pointer.object length 0 after initialized ∧
      WordArrayRep initialized pointer.object length (fun _=>0) := by
  obtain ⟨mode,present⟩ := calloc_prefix_zero host born
  obtain ⟨initialized,trace,host',words,_⟩ := zero_trace_exists length 0 pointer.object length after
    (by omega) mode present
  refine ⟨initialized,trace,host',?_,?_⟩
  · simpa only [zeroPrefix_full] using words
  · intro i hi
    norm_num

#print axioms zero_trace_exists
#print axioms calloc_to_zero_words
end RH080Next.FFTPV.WordArrays
