/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTDivideBody
import ExplicitFFTIncrementFrame
import ExplicitApplicationPureCall
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.DivideSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings
open FFT.Limbs
open IncrementSource (base)

def incrementStatement : Stmt:=.returnValue (some (.call "increment_words" [.variable "a",.variable "n"]))
def remainderTest : Expr:=.binary .gt (.variable "rem") (.literal (.integer 0 "ULL"))
def ceilingTest : Expr:=.binary .gt (.variable "ceiling") (.literal (.integer 0 "ULL"))
def remainderBranch : Stmt:=.ite remainderTest (.block [incrementStatement]) none
def roundingStatement : Stmt:=.ite ceilingTest (.block [remainderBranch]) none

def roundedData (old : Nat → Nat) (start n d ceiling : Nat) : Nat → Nat :=
  if 0 < ceiling ∧ 0 < (division old start n d 0).2
  then IncrementSource.currentData (currentData old start n d 0) start n
  else currentData old start n d 0

theorem full_frame_as_birth {F : Type} {a b : State F} {object : Nat}
    (h : IncrementSource.FullCallerFrame a b object) :
    ApplicationBirthFrame.Frame a.nextObject a b [object] :=
  ⟨h.well,h.nextObject,h.nextObject,h.nextScope,h.mode,h.foreign,
    fun i old absent=>h.objects i old (by simpa using absent)⟩

theorem close_full_frame {F : Type} {before middle : State F} {object : Nat}
    (well : WellScoped before) (h : IncrementSource.FullCallerFrame before.enterScope middle object) :
    IncrementSource.FullCallerFrame before
      {middle.leaveScope before.nextScope before.environment with scope:=before.scope} object := by
  have fr:=ApplicationBirthFrame.close_frame well (le_refl _) (full_frame_as_birth h)
  refine ⟨⟨rfl,rfl,fr.foreign,fr.well,fun i hi hn=>fr.outside i hi (by simpa using hn)⟩,
    fr.nextObject,fr.nextScope,fr.mode⟩

theorem full_frame_refl {F : Type} {state : State F} (object : Nat) (well : WellScoped state) :
    IncrementSource.FullCallerFrame state state object :=
  ⟨⟨rfl,rfl,rfl,well,fun _ _ _=>rfl⟩,le_refl _,le_refl _,rfl⟩

theorem ceiling_eval {F : Type} (context : Context F) {state : State F}
    {object length start n d ceiling owner j : Nat} {li : Var → Nat} {old : Nat → Nat}
    (h : View state object length start n d ceiling owner li old j) :
    Eval context state ceilingTest (.integer (.boolean (decide (0 < ceiling)))) state :=
  .binaryLR (.variable (h.locals.lookup Var.ceiling) (h.locals.read Var.ceiling))
    (.literal (.integer 0 "ULL") _ (.integer (integer64 0)) (by rfl))
    (by simp only [values,binary,CompareSource.binary64_gt ceiling 0 (by have hc:=h.ceiling_bound; omega)
      (by norm_num),Option.map_some])

theorem remainder_eval {F : Type} (context : Context F) {state : State F}
    {object length start n d ceiling owner j : Nat} {li : Var → Nat} {old : Nat → Nat}
    (h : View state object length start n d ceiling owner li old j) :
    Eval context state remainderTest (.integer (.boolean (decide (0 < (division old start n d j).2)))) state := by
  have hr:=division_remainder_lt old start n d j h.divisor_positive
  have hd:=h.divisor_bound
  exact .binaryLR (.variable (h.locals.lookup Var.rem) (h.locals.read Var.rem))
    (.literal (.integer 0 "ULL") _ (.integer (integer64 0)) (by rfl))
    (by simp only [values,binary,CompareSource.binary64_gt (division old start n d j).2 0
      (by dsimp [base] at hd; omega) (by norm_num),Option.map_some])

theorem quotient_digits {F : Type} {state : State F}
    {object length start n d ceiling owner : Nat} {li : Var → Nat} {old : Nat → Nat}
    (h : View state object length start n d ceiling owner li old 0) :
    ∀i < n,currentData old start n d 0 (start+i) < base := by
  intro i hi
  rw [currentData_slice old start n d i hi]
  exact divideDigits_bounds base d n (by norm_num [base]) h.divisor_positive _ h.digits i hi

/-- Ceiling correction cannot overflow: the rounded quotient is no larger
than the original positive encoded integer, itself below the target capacity. -/
theorem rounded_increment_carry_zero {F : Type} {state : State F}
    {object length start n d ceiling owner : Nat} {li : Var → Nat} {old : Nat → Nat}
    (h : View state object length start n d ceiling owner li old 0)
    (positive : 0 < (division old start n d 0).2) :
    (incrementDigits base (fun i=>currentData old start n d 0 (start+i)) n).2=0 := by
  have original_lt:=magnitude_lt base n (by norm_num [base]) (fun i=>old (start+i)) h.digits
  have exactValue:=currentData_value old start n d
  have hd:=h.divisor_positive
  have small : magnitude base n (fun i=>currentData old start n d 0 (start+i))+1 < base^n := by
    have hm:=Nat.mul_le_mul_right (magnitude base n (fun i=>currentData old start n d 0 (start+i)))
      (show 1 ≤ d by omega)
    nlinarith
  exact (incrementDigits_no_overflow base n (by norm_num [base]) _ small).1

#print axioms close_full_frame
#print axioms rounded_increment_carry_zero
end RH080Next.FFTPV.DivideSource
