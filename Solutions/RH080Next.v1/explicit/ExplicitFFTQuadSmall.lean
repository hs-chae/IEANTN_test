/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTQuadMagnitude
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.QuadSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings
open InputLoader RootSource

/-- Actual multiply_small, with its returned overflow discharged from a proved
integer capacity bound. Factor zero is expressly included. -/
theorem multiply_small_zero {F : Type} (context : Context F)
    (selected : findFunction context.program "multiply_small"=some FFTRecursivePV.multiply_small_ast)
    (before : State F) (object size start n multiplier : Nat) (old : Nat → Nat)
    (well : WellScoped before) (array : WordArrayRep before object size old)
    (bound : start+n≤ size) (small : n≤6) (digits : ∀k< n,old (start+k)< base) (factorSmall : multiplier< base)
    (capacity : multiplier*FFT.Limbs.magnitude base n (fun k=> old (start+k))< base^n) :
    ∃after,Call context "multiply_small" [.pointer (wordPointer object start),.integer (integer64 n),.integer (integer64 multiplier)]
      before (.value (.integer (integer64 0))) after ∧
      EveryCall context before "multiply_small" [.pointer (wordPointer object start),.integer (integer64 n),.integer (integer64 multiplier)]
        (.value (.integer (integer64 0))) after ∧
      WordArrayRep after object size (MultiplySmallSource.currentData old start multiplier n) ∧
      MultiplyCall.CallerFrame before after [object] ∧
      (∀k< n,MultiplySmallSource.currentData old start multiplier n (start+k)< base) ∧
      FFT.Limbs.magnitude base n (fun k=> MultiplySmallSource.currentData old start multiplier n (start+k))=
        multiplier*FFT.Limbs.magnitude base n (fun k=> old (start+k)) ∧
      ∀k,(k< start ∨ start+n≤ k) → MultiplySmallSource.currentData old start multiplier n k=old k:=by
  obtain ⟨after,called,rep,frame⟩:=MultiplySmallSource.multiply_small_call_framed context selected before object size start n multiplier old well array bound small digits factorSmall
  have conservation:=MultiplySmallSource.currentData_value old start multiplier n
  have zero : (MultiplySmallSource.scaledRow old start multiplier n).2=0:=by
    change FFT.Limbs.magnitude base n (fun k=> MultiplySmallSource.currentData old start multiplier n (start+k))+
      (MultiplySmallSource.scaledRow old start multiplier n).2*base^n=multiplier*FFT.Limbs.magnitude base n (fun k=> old (start+k)) at conservation
    have positive : 0< base^n:=pow_pos (by norm_num [base]) _
    nlinarith
  rw [zero] at called
  have value : FFT.Limbs.magnitude base n (fun k=> MultiplySmallSource.currentData old start multiplier n (start+k))=
      multiplier*FFT.Limbs.magnitude base n (fun k=> old (start+k)):=by simpa only [zero,Nat.zero_mul,Nat.add_zero,MultiplySmallSource.base,base] using conservation
  exact ⟨after,called,fun state result actual=> MultiplySmallSource.returned_call_unique selected called actual,rep,small_caller frame,
    (fun k hk=> by rw [MultiplySmallSource.currentData_slice old start multiplier n k hk];exact MultiplySmallSource.processed_digit_bound old start multiplier n k hk),value,
    fun k hk=> by simp [MultiplySmallSource.currentData,show ¬(start≤ k ∧ k< start+n) by omega]⟩

theorem View.factor_evaluation {F : Type} (context : Context F) {before : State F} {input : InputLoader.Input} {workObject fo bo j cutoff : Nat}
    {ids : InputLoader.Var → Nat} {auxIds : Aux → Nat} {dataMemory workData : Nat → Nat}
    (h : View before input workObject fo bo 2 j cutoff ids auxIds (absoluteValues input j) dataMemory workData) :
    Eval context before factorExpression (.integer (integer64 (factor j))) before:=by
  have count:=count_bound input.profile
  have active:=h.body.active
  have jBound : j≤2520:=by omega
  have j64 : j<2^64:=by omega
  have product : 20*j<2^64:=by omega
  have final : factor j<2^64:=lt_trans (factor_bound input.profile j active) (by norm_num [base])
  have jRead:=h.body.parameter_eval context .j
  have first : Eval context before (.paren (.binary .mul (.literal (.integer 20 "ULL")) (.variable "j"))) (.integer (integer64 (20*j))) before:=
    .paren (.binaryLR (.literal _ _ _ (by rfl)) jRead (by
      change Option.map Value.integer (Integer.binary .mul (integer64 20) (integer64 j))=_
      rw [binary64_mul 20 j (by norm_num) j64 product];rfl))
  exact .paren (.binaryLR first jRead (by
    change Option.map Value.integer (Integer.binary .mul (integer64 (20*j)) (integer64 j))=_
    rw [binary64_mul (20*j) j product j64 final];rfl))

#print axioms multiply_small_zero
#print axioms View.factor_evaluation
end RH080Next.FFTPV.QuadSource
