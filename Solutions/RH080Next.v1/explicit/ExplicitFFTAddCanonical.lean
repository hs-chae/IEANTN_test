/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTAddArithmetic
import FFTCanonicalSourceFinal
import FFTCanonicalDeterminism
import ExplicitApplicationExpressionCall
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.AddSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings
open FFT.Limbs
open IncrementSource (base)

def finalData (input : Input) : Nat → Nat:=CanonicalSource.canonicalData (rawData input) (input.layout.start .out)

structure FinishedView {F : Type} (state : State F) (input : Input) (owner : Nat) (li : Var → Nat) : Prop where
  array : WordArrayRep state (input.layout.object .out) (input.layout.length (input.layout.object .out)) (finalData input)
  locals : Locals state name type li owner (values input 5 (rawStatus input))
  separate : ∀v,input.layout.object .out≠li v
  well : WellScoped state

/-- The actual canonical_sign source call consumes the actual arithmetic
output, preserves the function's return-status local, and normalizes zero. -/
theorem canonical_execution {F : Type} (context : Context F)
    (selected : findFunction context.program "canonical_sign"=some FFTRecursivePV.canonical_sign_ast)
    {before : State F} {input : Input} {owner : Nat} {li : Var → Nat}
    (h : ArithmeticView before input owner li) (scope : before.scope=owner) :
    ∃after,Exec context before canonicalStatement .normal after ∧ FinishedView after input owner li ∧
      CopyLoop.CallerFrame before after (input.layout.object .out) := by
  obtain ⟨after,called,rep,frame,total⟩:=CanonicalSource.canonical_sign_total context selected before
    (input.layout.object .out) (input.layout.length (input.layout.object .out)) (input.layout.start .out)
    (rawData input) h.well h.array (input.layout.bound .out) (rawData_digits input)
  have args : Args context before [.variable "out"]
      [.pointer (wordPointer (input.layout.object .out) (input.layout.start .out))] before := by
    apply Args.ordered (order:=[(0,.variable "out")])
      (evaluated:=[(0,.pointer (wordPointer (input.layout.object .out) (input.layout.start .out)))])
    · exact List.Perm.refl _
    · exact .cons (.variable (h.locals.lookup Var.out) (h.locals.read Var.out)) .nil
    · change List.Forall₂ _ [0] _
      exact .cons rfl .nil
  have lm : Locals after name type li owner (values input 5 (rawStatus input)) := by
    refine ⟨?_,?_,h.locals.distinct,?_⟩
    · rw [frame.environment]
      exact h.locals.lookup
    · intro v
      refine ⟨(h.locals.slots v).storable,?_⟩
      rw [frame.objects _ (h.well.objectIds _ _ (h.locals.slots v).object) (h.separate v).symm]
      exact (h.locals.slots v).object
    · rw [←scope,←frame.scope]
      exact frame.well.current
  exact ⟨after,.expression (.call args called),⟨rep,lm,h.separate,frame.well⟩,frame⟩

#print axioms canonical_execution
end RH080Next.FFTPV.AddSource
