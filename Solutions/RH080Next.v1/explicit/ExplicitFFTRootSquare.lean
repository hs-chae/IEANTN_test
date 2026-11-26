/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTRootModel
import FFTFixedMultiplyCorrectWords
import FFTStatusCall
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.RootSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings
open IncrementSource (base)
open FFT.Limbs

def offsetExpr (name : String) (offset : Nat) : Expr:=
  .paren (.binary .add (.variable name) (.literal (.integer offset "ULL")))

def squareArguments : List Expr:=[offsetExpr "work" 6,.variable "work",.variable "work",offsetExpr "work" 36]
def squareStatement : Stmt:=StatusCall.statement "fixed_multiply" squareArguments

theorem xData_small (input : Input) :
    magnitude base 5 (fun k=>xData input (input.layout.workStart+k))≤1000*10^36 := by
  rw [xData_value]
  have h:=Nat.div_le_self (2*FFT.IntegerModel.piInteger.toNat) input.n
  exact h.trans (by norm_num [FFT.IntegerModel.piInteger];decide)

/-- Actual first fixed_multiply source call computes x²/unit at work+6,
including arbitrary shared-object caller layout and real status assignment.
Untouched-word preservation consumes the separate actual source slice theorem. -/
theorem square_execution {F : Type} (context : Context F)
    (selected : findFunction context.program "fixed_multiply"=some fixed_multiply_ast)
    (zeroSelected : findFunction context.program "zero_words"=some zero_words_ast)
    (incrementSelected : findFunction context.program "increment_words"=some increment_words_ast)
    (canonicalSelected : findFunction context.program "canonical_sign"=some FFTRecursivePV.canonical_sign_ast)
    {before : State F} {input : Input} {owner statusId : Nat} {ids : Param → Nat}
    (h : ScaleView before input owner statusId ids (xData input)) (scope : before.scope=owner) :
    ∃after data,Exec context before squareStatement .normal after ∧
      ScaleView after input owner statusId ids data ∧ after.scope=owner ∧
      CanonicalSource.represented data (input.layout.workStart+6)=x2Integer input.n ∧
      (∀k < 5,data (input.layout.workStart+6+k)<base) ∧ data (input.layout.workStart+11)≤1 ∧
      ∀k,k < input.layout.size → (k < input.layout.workStart+6 ∨ input.layout.workStart+12≤k) →
        (k < input.layout.workStart+36 ∨ input.layout.workStart+46≤k) → data k=xData input k := by
  have workBound:=input.layout.workBound
  have digits:=xData_digits input
  have bit : xData input (input.layout.workStart+5)≤1:=by rw [xData_zero_work input 5 (by omega) (by omega)];omega
  have small:=xData_small input
  obtain ⟨after,data,called,post,math,normalized,sign,workWords,outWords,frame,every⟩:=MultiplyCall.fixed_multiply_correct_words context
    selected zeroSelected incrementSelected canonicalSelected before
    input.layout.object input.layout.size (input.layout.workStart+6)
    input.layout.object input.layout.size input.layout.workStart
    input.layout.object input.layout.size input.layout.workStart
    input.layout.object input.layout.size (input.layout.workStart+36)
    (xData input) (xData input) (xData input) (xData input) h.params.well
    h.params.array h.params.array h.params.array h.params.array (fun _=>rfl) (fun _=>rfl) (fun _=>rfl)
    (Or.inr (Or.inl (by omega))) (Or.inr (Or.inl (by omega))) (Or.inr (Or.inl (by omega)))
    (by omega) (by omega) (by omega) (by omega) digits digits bit bit small small
  have objects : ∀id,id < before.nextObject → id≠input.layout.object → after.objects id=before.objects id:=by
    intro id old separate;exact frame.frame.outside id old (by simp [separate])
  have view:=h.params.reframe post frame.environment scope frame.scope frame.frame.well objects
  have status : Slot after statusId owner .u64 (.integer (integer64 0)):=by
    refine ⟨h.status.storable,?_⟩
    rw [objects _ (h.params.well.objectIds _ _ h.status.object) h.statusSeparate.symm];exact h.status.object
  have lookup : after.environment.lookup "status"=some (scalarPointer statusId .u64):=by
    rw [frame.environment];exact h.statusLookup
  have readOffset (k : Nat) (hk : input.layout.workStart+k< input.layout.size) (k64 : k<2^64) :
      Eval context before (offsetExpr "work" k) (.pointer (wordPointer input.layout.object (input.layout.workStart+k))) before:=by
    apply Eval.paren
    apply Eval.binaryLR (.variable (h.params.locals.lookup Param.work) (h.params.locals.read Param.work))
      (.literal (.integer k "ULL") _ (.integer (integer64 k)) ?_)
    · simp only [paramValue,binary,slice_pointer_add h.params.array hk,Option.map_some]
    · have fit : k<18446744073709551616:=k64;simp [Literal.value,integer64,fit]
  have args : Args context before squareArguments
      [.pointer (wordPointer input.layout.object (input.layout.workStart+6)),
       .pointer (wordPointer input.layout.object input.layout.workStart),
       .pointer (wordPointer input.layout.object input.layout.workStart),
       .pointer (wordPointer input.layout.object (input.layout.workStart+36))] before:=by
    apply Args.ordered (order:=[(0,offsetExpr "work" 6),(1,.variable "work"),(2,.variable "work"),(3,offsetExpr "work" 36)])
      (evaluated:=[(0,.pointer (wordPointer input.layout.object (input.layout.workStart+6))),
        (1,.pointer (wordPointer input.layout.object input.layout.workStart)),
        (2,.pointer (wordPointer input.layout.object input.layout.workStart)),
        (3,.pointer (wordPointer input.layout.object (input.layout.workStart+36)))])
    · exact List.Perm.refl _
    · exact .cons (readOffset 6 (by omega) (by norm_num))
        (.cons (.variable (h.params.locals.lookup Param.work) (h.params.locals.read Param.work))
          (.cons (.variable (h.params.locals.lookup Param.work) (h.params.locals.read Param.work))
            (.cons (readOffset 36 (by omega) (by norm_num)) .nil)))
    · change List.Forall₂ _ [0,1,2,3] _;exact .cons rfl (.cons rfl (.cons rfl (.cons rfl .nil)))
  have run:=StatusCall.assignment_execution h.statusLookup lookup h.status status args called
  have output : CanonicalSource.represented data (input.layout.workStart+6)=x2Integer input.n:=by
    rw [xData_integer] at math
    change _=x2Integer input.n at math
    exact math
  refine ⟨after,data,run,⟨view,status,lookup,h.statusSeparate⟩,frame.scope.trans scope,output,normalized,(by simpa [Nat.add_assoc] using sign),?_⟩
  intro k hk outOutside scratchOutside
  exact outWords k hk (by simpa [Nat.add_assoc] using outOutside) (Or.inr (by simpa [Nat.add_assoc] using scratchOutside))

#print axioms xData_small
#print axioms square_execution
end RH080Next.FFTPV.RootSource
