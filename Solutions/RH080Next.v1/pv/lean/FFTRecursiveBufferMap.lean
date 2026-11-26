/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTRecursiveLoopBindings
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.RecursiveSource

/-- Actual allocation identity selects the caller's complete word extent. -/
def bufferLength {total : Nat} (b : Buffers total) (object : Nat) : Nat :=
  if object=b.object .output then b.length .output else
  if object=b.object .input then b.length .input else
  if object=b.object .twiddle then b.length .twiddle else
  if object=b.object .work then b.length .work else 0

def dataByObject {total : Nat} (b : Buffers total) (input table output work : Nat → Nat)
    (object : Nat) : Nat → Nat :=
  if object=b.object .output then output else
  if object=b.object .input then input else
  if object=b.object .twiddle then table else
  if object=b.object .work then work else fun _ => 0

@[simp] theorem buffer_object_eq {total : Nat} (b : Buffers total) (r s : Buffer) :
    b.object r = b.object s ↔ r=s := ⟨fun h => b.distinct h,congrArg b.object⟩

@[simp] theorem bufferLength_object {total : Nat} (b : Buffers total) (r : Buffer) :
    bufferLength b (b.object r) = b.length r := by
  cases r <;> simp [bufferLength]

@[simp] theorem dataByObject_object {total : Nat} (b : Buffers total)
    (input table output work : Nat → Nat) (r : Buffer) :
    dataByObject b input table output work (b.object r) = bufferData input table output work r := by
  cases r <;> simp [dataByObject,bufferData]

#print axioms dataByObject_object
end RH080Next.FFTPV.RecursiveSource
