/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTDropTwoLoop
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.DropTwoSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings

def clear (k : Nat) : Stmt:=.assign (.index (.variable "total") (.literal (.integer k "ULL"))) (.literal (.integer 0 "ULL"))

theorem actual_clear_four : (ProductRow.items FFTRecursivePV.w4_recursive_norm_upper_ast.body)[29]?=some (clear 4):=by rfl
theorem actual_clear_five : (ProductRow.items FFTRecursivePV.w4_recursive_norm_upper_ast.body)[30]?=some (clear 5):=by rfl

theorem clear_one {F : Type} (context : Context F) {before : State F}
    {workObject owner : Nat} {ids : Var→Nat} {old current : Nat→Nat} (k : Nat) (hk : k<6)
    (array : WordArrayRep before workObject 512 current)
    (locals : Locals before name type ids owner (values workObject old 4))
    (separate : ∀v,workObject≠ids v) (well : WellScoped before) :
    ∃after,Exec context before (clear k) .normal after ∧
      WordArrayRep after workObject 512 (Function.update current (192+k) 0) ∧
      Locals after name type ids owner (values workObject old 4) ∧ WellScoped after ∧
      ScanFrame.Frame before after [workObject,ids Var.i] := by
  have bound : 192+k<512:=by omega
  obtain ⟨after,written,rep⟩:=word_store_with_rep array bound (show 0<2^64 by norm_num)
  have literal : Eval context before (.literal (.integer k "ULL")) (.integer (integer64 k)) before :=
    .literal _ _ _ (by simp [Literal.value,integer64];omega)
  have run : Exec context before (clear k) .normal after:=by
    apply Exec.assign (value:=.integer (integer64 0)) (.literal (.integer 0 "ULL") _ _ (by rfl))
      (.index (.variable (locals.lookup Var.total) (locals.read Var.total)) literal (slice_pointer_add array bound))
    exact written
  exact ⟨after,run,rep,ApplicationBirthFrame.locals_store_other locals (fun v=>(separate v).symm) written,
    wellScoped_store well written,ScanFrame.Frame.store (by simp [wordPointer]) written⟩

theorem clear_execution {F : Type} (context : Context F) {before : State F}
    {workObject owner : Nat} {ids : Var→Nat} {old : Nat→Nat}
    (h : View before workObject ids owner 4 old) :
    ∃after,ExecList context before [clear 4,clear 5] .normal after ∧
      WordArrayRep after workObject 512 (dropped old 192) ∧
      Locals after name type ids owner (values workObject old 4) ∧ WellScoped after ∧
      ScanFrame.Frame before after [workObject,ids Var.i] := by
  obtain ⟨middle,first,array,params,wm,firstFrame⟩:=clear_one context 4 (by norm_num) h.array h.locals h.separate h.well
  obtain ⟨after,second,rep,locals,wa,secondFrame⟩:=clear_one context 5 (by norm_num) array params h.separate wm
  exact ⟨after,.cons first (.cons second .nil),rep,locals,wa,firstFrame.trans secondFrame⟩

theorem dropped_normalized {old : Nat→Nat} {start : Nat} (digits : ∀k,k<6 → old (start+k)<base) :
    ∀k,k<6 → dropped old start (start+k)<base := by
  intro k hk
  rw [dropped_digits old start k hk]
  split
  · rename_i h
    have d:=digits (k+2) (by omega)
    simpa only [Nat.add_assoc] using d
  · norm_num [base]

theorem dropped_capacity {old : Nat→Nat} {start : Nat} (digits : ∀k,k<6 → old (start+k)<base) :
    FFT.Limbs.magnitude base 6 (fun k=>dropped old start (start+k))+1<base^6:=by
  rw [dropped_magnitude digits]
  have bound:=FFT.Limbs.magnitude_lt base 6 (by norm_num [base]) (fun k=>old (start+k)) digits
  norm_num [base] at bound ⊢
  omega

#print axioms clear_one
#print axioms clear_execution
#print axioms dropped_normalized
#print axioms dropped_capacity
end RH080Next.FFTPV.DropTwoSource
