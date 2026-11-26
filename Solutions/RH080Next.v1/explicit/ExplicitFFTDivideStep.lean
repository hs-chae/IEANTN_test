/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTDivideBase
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.DivideSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings
open FFT.Limbs
open IncrementSource (base)

def writes (object : Nat) (li : Var → Nat) : List Nat := [object,li .j,li .rem]

theorem condition_eval {F : Type} (context : Context F) {state : State F}
    {object length start n d ceiling owner j : Nat} {li : Var → Nat} {old : Nat → Nat}
    (h : View state object length start n d ceiling owner li old j) :
    Eval context state condition (.integer (.boolean (decide (0 < j)))) state := by
  exact .binaryLR (.variable (h.locals.lookup Var.j) (h.locals.read Var.j))
    (.literal (.integer 0 "ULL") _ (.integer (integer64 0)) (by rfl))
    (by simp only [values,binary,CompareSource.binary64_gt j 0 (by have hn:=h.small; have hj:=h.active; omega)
      (by norm_num),Option.map_some])

theorem values_j_update (object start n d ceiling j r k : Nat) :
    Function.update (values object start n d ceiling j r) .j (.integer (integer64 k))=
      values object start n d ceiling k r := by funext i; cases i <;> rfl

theorem decrement_execution {F : Type} (context : Context F) {before : State F}
    {object length start n d ceiling owner j : Nat} {li : Var → Nat} {old : Nat → Nat}
    (h : View before object length start n d ceiling owner li old (j+1)) :
    ∃after,Exec context before decrement .normal after ∧
      WordArrayRep after object length (currentData old start n d (j+1)) ∧
      Locals after name type li owner (values object start n d ceiling j (division old start n d (j+1)).2) ∧
      ApplicationBirthFrame.Frame before.nextObject before after (writes object li) := by
  have hj64 : j+1 < 2^64 := by have hn:=h.small; have hj:=h.active; omega
  have storable:=ZeroFrame.u64_storable j (by omega)
  obtain ⟨after,stored⟩:=IncrementSource.slot_store_exists (h.locals.slots Var.j) (.integer (integer64 j)) storable
  have run : Exec context before decrement .normal after := by
    apply Exec.assign (value:=.integer (integer64 j))
      (Eval.paren (Eval.binaryLR (.variable (h.locals.lookup Var.j) (h.locals.read Var.j))
        (.literal (.integer 1 "ULL") _ (.integer (integer64 1)) (by rfl))
        (by simp only [values,binary,CompareSource.binary64_sub_one j hj64,Option.map_some])))
      (Place.variable (h.locals.lookup Var.j))
    exact stored
  have locals : Locals after name type li owner (values object start n d ceiling j (division old start n d (j+1)).2) := by
    simpa only [values_j_update] using h.locals.store Var.j (.integer (integer64 j)) storable stored
  exact ⟨after,run,IncrementSource.array_store_other h.array (h.separate Var.j) stored,locals,
    ApplicationBirthFrame.store_frame _ _ h.well (le_refl _) (Or.inl (by simp [writes,scalarPointer])) stored⟩

/-- Three actual statements: safe decrement, temporary t birth, and in-place
quotient digit. No lower unread word is overwritten by the reverse scan. -/
theorem digit_prefix_execution {F : Type} (context : Context F) {before : State F}
    {object length start n d ceiling owner j : Nat} {li : Var → Nat} {old : Nat → Nat}
    (h : View before object length start n d ceiling owner li old (j+1)) :
    ∃after tId tOwner,
      ExecList context before [decrement,.declare .u64 "t" (some tExpr),digitStmt] .normal after ∧
      WordArrayRep after object length (currentData old start n d j) ∧
      Locals after name type li owner (values object start n d ceiling j (division old start n d (j+1)).2) ∧
      Slot after tId tOwner .u64
        (.integer (integer64 ((division old start n d (j+1)).2*base+old (start+j)))) ∧
      after.environment.lookup "t"=some (scalarPointer tId .u64) ∧
      ApplicationBirthFrame.Frame before.nextObject before after (writes object li) := by
  obtain ⟨tested,dec,rt,lt,first⟩:=decrement_execution context h
  have hj : j < n := by have hn:=h.active; omega
  let r:=(division old start n d (j+1)).2
  let t:=r*base+old (start+j)
  have hr : r < d:=division_remainder_lt old start n d (j+1) h.divisor_positive
  have hd:=h.digits j hj
  have hdb:=h.divisor_bound
  have ht : t < 2^64 := by dsimp [t,base]; dsimp [base] at hdb hd; omega
  have hp : r*base < 2^64 := by dsimp [base]; dsimp [base] at hdb; omega
  have hr64 : r < 2^64 := by dsimp [base] at hdb; omega
  have hd64 : old (start+j) < 2^64 := by dsimp [base] at hd; omega
  have hi : start+j < length := by have hb:=h.bound; omega
  have readA : Eval context tested (.index (.variable "a") (.variable "j"))
      (.integer (integer64 (old (start+j)))) tested := by
    have run : Eval context tested (.index (.variable "a") (.variable "j"))
        (.integer (integer64 (currentData old start n d (j+1) (start+j)))) tested :=
      .load (.index (.variable (lt.lookup Var.a) (lt.read Var.a))
        (.variable (lt.lookup Var.j) (lt.read Var.j)) (slice_pointer_add rt hi)) (word_load rt hi)
    simpa only [currentData_unread] using run
  have readR : Eval context tested (.variable "rem") (.integer (integer64 r)) tested:=
    .variable (lt.lookup Var.rem) (lt.read Var.rem)
  have product : Eval context tested (.paren (.binary .mul (.variable "rem")
      (.literal (.integer 1000000000 "ULL")))) (.integer (integer64 (r*base))) tested:=
    .paren (.binaryLR readR
      (.literal (.integer 1000000000 "ULL") _ (.integer (integer64 base)) (by rfl))
      (by simp only [binary,binary64_mul r base hr64 (by norm_num [base]) hp,Option.map_some]))
  have readT : Eval context tested tExpr (.integer (integer64 t)) tested:=
    .paren (.binaryLR product readA
      (by simp only [binary,binary64_add (r*base) (old (start+j)) hp hd64 ht,Option.map_some,t]))
  obtain ⟨middle,declared⟩:=ZeroFrame.declare_exists first.well .u64 "t" (.integer (integer64 t))
    (ZeroFrame.u64_storable t ht)
  have dt:=declare_storable (ZeroFrame.u64_storable t ht) (convert64 t ht) declared
  have lm:=ApplicationBirthFrame.locals_declare_old first.well lt (by intro i; cases i <;> decide) dt
  have rm:=ApplicationBirthFrame.array_declare_old first.well rt dt
  have tNamed : middle.environment.lookup "t"=some (scalarPointer tested.nextObject .u64) := by rw [dt.environment]; rfl
  have readTM : Eval context middle (.variable "t") (.integer (integer64 t)) middle:=.variable tNamed dt.slot.read
  have d64 : d < 2^64 := by dsimp [base] at hdb; omega
  have q64 : t/d < 2^64 := lt_of_le_of_lt (Nat.div_le_self _ _) ht
  obtain ⟨after,stored,ra⟩:=word_store_with_rep rm hi q64
  have storeRun : Exec context middle digitStmt .normal after := by
    apply Exec.assign (value:=.integer (integer64 (t/d)))
      (Eval.paren (.binaryLR readTM (.variable (lm.lookup Var.d) (lm.read Var.d))
        (by simp only [values,binary,binary64_div t d ht d64 h.divisor_positive,Option.map_some])))
      (Place.index (.variable (lm.lookup Var.a) (lm.read Var.a))
        (.variable (lm.lookup Var.j) (lm.read Var.j)) (slice_pointer_add rm hi))
    exact stored
  have la:=ApplicationBirthFrame.locals_store_other lm (fun i=>(h.separate i).symm) stored
  have oldObj:=first.well.objectIds object _ rt.2.1
  have ta:=ApplicationBirthFrame.slot_store_other dt.slot (by change tested.nextObject≠object; omega) stored
  have second:=ApplicationBirthFrame.declare_frame before.nextObject (writes object li) first.well first.fresh declared
  have third:=ApplicationBirthFrame.store_frame before.nextObject (writes object li) (wellScoped_declare first.well declared)
    (by rw [dt.nextObject]; exact Nat.le_trans first.fresh (Nat.le_succ _))
    (Or.inl (by simp [writes,wordPointer])) stored
  refine ⟨after,tested.nextObject,tested.scope,.cons dec (.cons (.declareSome readT declared) (.cons storeRun .nil)),?_,la,ta,?_,first.trans (second.trans third)⟩
  · simpa only [t,r,currentData_step old start n d j hj] using ra
  · rw [(SourceLocals.store_frame stored).1]
    exact tNamed

#print axioms condition_eval
#print axioms decrement_execution
#print axioms digit_prefix_execution
end RH080Next.FFTPV.DivideSource
