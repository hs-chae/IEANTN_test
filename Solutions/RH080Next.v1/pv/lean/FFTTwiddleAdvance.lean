/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTTwiddleStep
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.TwiddleSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings

theorem advance_execution {F : Type} (context : Context F) {before : State F}
    {tableObject workObject n owner j : Nat} {ids : Var→Nat} {tableData workData : Nat→Nat} {seed : FFT.IntegerModel.CInt}
    (h : View before tableObject workObject n ids owner j tableData workData seed) (inside : j<n/2)
    (newValue : ComplexSource.pair tableData (j*12)=sequence seed j)
    (newDigits : ∀c : Fin 2,∀d,d<5 → tableData (j*12+6*c.val+d)<1000000000)
    (newSigns : ∀c : Fin 2,tableData (j*12+6*c.val+5)≤1) :
    ∃after,Exec context before advance .normal after ∧
      View after tableObject workObject n ids owner (j+1) tableData workData seed ∧
      ScanFrame.Frame before after [ids Var.j] := by
  have hj : j+1<2^64 := by have b:=h.nbound;omega
  obtain ⟨after,written⟩ := ProductInner.slot_store_exists (h.locals.slots Var.j)
    (.integer (integer64 (j+1))) (ZeroFrame.u64_storable (j+1) hj)
  have run : Exec context before advance .normal after := by
    apply Exec.assign (value:=.integer (integer64 (j+1)))
      (Eval.paren (Eval.binaryLR (.variable (h.locals.lookup Var.j) (h.locals.read Var.j))
        (.literal (.integer 1 "ULL") _ (.integer (integer64 1)) (by rfl))
        (by simp only [values,binary,binary64_add j 1 (by omega) (by norm_num) hj,Option.map_some])))
      (.variable (h.locals.lookup Var.j))
    exact written
  have params := h.locals.store Var.j (.integer (integer64 (j+1))) (ZeroFrame.u64_storable (j+1) hj) written
  have eq : Function.update (values tableObject workObject n j) Var.j (.integer (integer64 (j+1)))=values tableObject workObject n (j+1) := by
    funext v;cases v <;> simp [values,Function.update]
  rw [eq] at params
  obtain ⟨_,mode,_,_,_,outside⟩ := store_frame written
  have table : WordArrayRep after tableObject (n/2*12) tableData :=
    ⟨mode.trans h.table.1,(outside tableObject (h.separate Var.j).1).trans h.table.2.1,h.table.2.2⟩
  have work : WordArrayRep after workObject 512 workData :=
    ⟨mode.trans h.work.1,(outside workObject (h.separate Var.j).2).trans h.work.2.1,h.work.2.2⟩
  have view : View after tableObject workObject n ids owner (j+1) tableData workData seed := by
    refine ⟨params,table,work,h.different,h.separate,h.nbound,by have a:=h.active;omega,?_,?_,?_,
      h.rootDigits,h.rootSigns,h.rootValue,h.rootSmall,h.valuesSmall,wellScoped_store h.well written⟩
    · intro k hk c d hd
      by_cases lt : k<j
      · exact h.tableDigits k lt c d hd
      · have ke : k=j := by omega
        subst k;exact newDigits c d hd
    · intro k hk c
      by_cases lt : k<j
      · exact h.tableSigns k lt c
      · have ke : k=j := by omega
        subst k;exact newSigns c
    · intro k hk
      by_cases lt : k<j
      · exact h.tableValues k lt
      · have ke : k=j := by omega
        subst k;exact newValue
  exact ⟨after,run,view,ScanFrame.Frame.store (by simp [scalarPointer]) written⟩

#print axioms advance_execution
end RH080Next.FFTPV.TwiddleSource
