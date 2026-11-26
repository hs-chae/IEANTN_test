/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTOutputSumStep
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.OutputSumSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings

theorem advance_execution {F : Type} (context : Context F) {before : State F}
    {outputObject workObject n owner i : Nat} {ids : Var→Nat} {outputData workData : Nat→Nat} {samples : Nat→FFT.IntegerModel.CInt}
    (h : View before outputObject workObject n ids owner i outputData workData samples true) (inside : i<n) :
    ∃after,Exec context before advance .normal after ∧
      View after outputObject workObject n ids owner (i+1) outputData workData samples ∧
      ScanFrame.Frame before after [ids Var.i] := by
  have hi : i+1<2^64:=by have b:=h.nbound;omega
  obtain ⟨after,written⟩:=ProductInner.slot_store_exists (h.locals.slots Var.i)
    (.integer (integer64 (i+1))) (ZeroFrame.u64_storable (i+1) hi)
  have run : Exec context before advance .normal after:=by
    apply Exec.assign (value:=.integer (integer64 (i+1)))
      (Eval.paren (Eval.binaryLR (.variable (h.locals.lookup Var.i) (h.locals.read Var.i))
        (.literal (.integer 1 "ULL") _ (.integer (integer64 1)) (by rfl))
        (by simp only [values,binary,binary64_add i 1 (by omega) (by norm_num) hi,Option.map_some])))
      (.variable (h.locals.lookup Var.i))
    exact written
  have params:=h.locals.store Var.i (.integer (integer64 (i+1))) (ZeroFrame.u64_storable (i+1) hi) written
  have eq : Function.update (values outputObject workObject n i) Var.i (.integer (integer64 (i+1)))=values outputObject workObject n (i+1):=by
    funext v;cases v <;> simp [values,Function.update]
  rw [eq] at params
  obtain ⟨_,mode,_,_,_,outside⟩:=store_frame written
  have output : WordArrayRep after outputObject (n*12) outputData:=
    ⟨mode.trans h.output.1,(outside outputObject (h.separate Var.i).1).trans h.output.2.1,h.output.2.2⟩
  have work : WordArrayRep after workObject 512 workData:=
    ⟨mode.trans h.work.1,(outside workObject (h.separate Var.i).2).trans h.work.2.1,h.work.2.2⟩
  refine ⟨after,run,⟨params,output,work,h.different,h.separate,h.nbound,by omega,h.outputDigits,h.outputValues,h.outputSmall,h.totalDigits,?_,wellScoped_store h.well written⟩,
    ScanFrame.Frame.store (by simp [scalarPointer]) written⟩
  simpa only [ite_true,partialSum_succ,Bool.false_eq_true,ite_false,Nat.add_zero] using h.totalValue

#print axioms advance_execution
end RH080Next.FFTPV.OutputSumSource
