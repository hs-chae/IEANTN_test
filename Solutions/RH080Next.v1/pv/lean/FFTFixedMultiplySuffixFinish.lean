/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTFixedMultiplySuffixRound
import FFTCanonicalSourceFinal
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.MultiplySuffix
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots ProductInner

/-- The true canonical_sign source helper is called before returning the
actual overflow slot. The final represented signed integer is unchanged. -/
theorem finish_execution {F : Type} (context : Context F)
    (selected : findFunction context.program "canonical_sign"=some FFTRecursivePV.canonical_sign_ast) {before : State F}
    {outObj outSize outStart workObj workSize workStart sign lost overflow : Nat}
    {ids owners : TVar → Nat} {outData scratch : Nat → Nat}
    (h : RoundView before outObj outSize outStart workObj workSize workStart ids owners outData scratch sign lost overflow) :
    ∃after,ExecList context before [canonicalCall,returnOverflow] (.returned (.integer (integer64 overflow))) after ∧
      WordArrayRep after outObj outSize (CanonicalSource.canonicalData outData outStart) ∧
      CanonicalSource.represented (CanonicalSource.canonicalData outData outStart) outStart =
        CanonicalSource.represented outData outStart ∧ CopyLoop.CallerFrame before after outObj := by
  obtain ⟨after,called,output,frame,every⟩:=CanonicalSource.canonical_sign_total context selected before
    outObj outSize outStart outData h.well h.output h.outBound h.digits
  have args : Args context before [v "out"] [.pointer (wordPointer outObj outStart)] before := by
    apply Args.ordered (order := [(0,v "out")]) (evaluated := [(0,.pointer (wordPointer outObj outStart))]) (by rfl)
    · exact .cons (.variable (h.locals.lookup (.inl MVar.out)) (h.locals.read (.inl MVar.out))) .nil
    · exact .cons (by rfl) .nil
  have run : Exec context before canonicalCall .normal after := .expression (.call args called)
  have oldSlot:=h.locals.slots (.inr ())
  have finalSlot : Slot after (ids (.inr ())) (owners (.inr ())) .u64 (.integer (integer64 overflow)) :=
    ⟨oldSlot.storable,(frame.objects _ (h.well.objectIds _ _ oldSlot.object)
      (h.separate (.inr ())).1.symm).trans oldSlot.object⟩
  have named : after.environment.lookup "overflow"=some (scalarPointer (ids (.inr ())) .u64) := by
    rw [frame.environment]
    exact h.locals.lookup (.inr ())
  have ret : Exec context after returnOverflow (.returned (.integer (integer64 overflow))) after :=
    .returnSome (.variable named finalSlot.read)
  exact ⟨after,.cons run (.abrupt ret (by intro eq;cases eq)),output,
    CanonicalSource.canonicalData_preserves outData outStart,frame⟩

#print axioms finish_execution
end RH080Next.FFTPV.MultiplySuffix
