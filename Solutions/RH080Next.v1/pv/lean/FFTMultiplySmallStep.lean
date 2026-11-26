/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTMultiplySmallBase
import FFTWordSubtraction
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.MultiplySmallSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings
open FFT.Limbs

def writes (object : Nat) (li : Var→Nat) : List Nat:=[object,li .j,li .carry]

theorem View.carry_bound {F : Type} {state : State F} {object length start n factor owner j : Nat}
    {li : Var→Nat} {old : Nat→Nat} (h : View state object length start n factor owner li old j) :
    (scaledRow old start factor j).2≤factor:=
  row_carry_le old start factor j (fun i hi=>h.digits i (lt_of_lt_of_le hi h.active))

theorem View.total_safe {F : Type} {state : State F} {object length start n factor owner j : Nat}
    {li : Var→Nat} {old : Nat→Nat} (h : View state object length start n factor owner li old j) (hj : j<n) :
    old (start+j)*factor+(scaledRow old start factor j).2<2^64:=by
  have hd:=h.digits j hj
  have hc:=h.carry_bound
  have productBound : old (start+j)*factor+(scaledRow old start factor j).2≤base*factor:=by
    have mul:=Nat.mul_le_mul_right factor (show old (start+j)+1≤base by omega)
    nlinarith
  have factorMax:=Nat.mul_lt_mul_of_pos_left h.factorSmall (by norm_num [base] : 0<base)
  exact productBound.trans_lt (factorMax.trans (by norm_num [base]))

theorem condition_eval {F : Type} (context : Context F) {state : State F}
    {object length start n factor owner j : Nat} {li : Var→Nat} {old : Nat→Nat}
    (h : View state object length start n factor owner li old j) :
    Eval context state condition (.integer (.boolean (decide (j<n)))) state:=by
  exact .binaryLR (.variable (h.locals.lookup Var.j) (h.locals.read Var.j))
    (.variable (h.locals.lookup Var.n) (h.locals.read Var.n))
    (by simp only [values,binary,binary64_lt j n (by have hj:=h.active;have hn:=h.small;omega)
      (by have hn:=h.small;omega),Option.map_some])

theorem t_eval {F : Type} (context : Context F) {state : State F}
    {object length start n factor owner j : Nat} {li : Var→Nat} {old : Nat→Nat}
    (h : View state object length start n factor owner li old j) (hj : j<n) :
    Eval context state tExpr
      (.integer (integer64 (old (start+j)*factor+(scaledRow old start factor j).2))) state:=by
  have index : start+j<length:=by have hb:=h.bound;omega
  have rd : Eval context state (.index (.variable "a") (.variable "j"))
      (.integer (integer64 (old (start+j)))) state:=by
    have got : Eval context state (.index (.variable "a") (.variable "j"))
        (.integer (integer64 (currentData old start factor j (start+j)))) state:=
      .load (.index (.variable (h.locals.lookup Var.a) (h.locals.read Var.a))
        (.variable (h.locals.lookup Var.j) (h.locals.read Var.j)) (slice_pointer_add h.array index))
        (word_load h.array index)
    simpa only [currentData_unread] using got
  have total:=h.total_safe hj
  have hd : old (start+j)<2^64:=by have hd:=h.digits j hj;dsimp [base] at hd;omega
  have hm : factor<2^64:=by have hm:=h.factorSmall;dsimp [base] at hm;omega
  have product : old (start+j)*factor<2^64:=by omega
  have carry : (scaledRow old start factor j).2<2^64:=by have hc:=h.carry_bound;omega
  have multiplied : Eval context state (.paren (.binary .mul (.index (.variable "a") (.variable "j")) (.variable "m")))
      (.integer (integer64 (old (start+j)*factor))) state:=
    .paren (.binaryLR rd (.variable (h.locals.lookup Var.m) (h.locals.read Var.m))
      (by simp only [values,binary,binary64_mul (old (start+j)) factor hd hm product,Option.map_some]))
  exact .paren (.binaryLR multiplied (.variable (h.locals.lookup Var.carry) (h.locals.read Var.carry))
    (by simp only [values,binary,binary64_add (old (start+j)*factor)
      (scaledRow old start factor j).2 product carry total,Option.map_some]))

/-- Actual temporary birth and in-place digit store. The prefix retains every
persistent function local, while the fresh t slot has its real block owner. -/
theorem digit_prefix_execution {F : Type} (context : Context F) {before : State F}
    {object length start n factor owner j : Nat} {li : Var → Nat} {old : Nat → Nat}
    (h : View before object length start n factor owner li old j) (hj : j < n) :
    ∃after,
      ExecList context before [.declare .u64 "t" (some tExpr),digitStmt] .normal after ∧
      WordArrayRep after object length (currentData old start factor (j+1)) ∧
      Locals after name type li owner
        (values object start n factor j (scaledRow old start factor j).2) ∧
      Slot after before.nextObject before.scope .u64
        (.integer (integer64 (old (start+j)*factor+(scaledRow old start factor j).2))) ∧
      after.environment.lookup "t"=some (scalarPointer before.nextObject .u64) ∧
      ApplicationBirthFrame.Frame before.nextObject before after (writes object li) := by
  let t:=old (start+j)*factor+(scaledRow old start factor j).2
  have hd:=h.digits j hj
  have hc:=h.carry_bound
  have ht : t < 2^64 := h.total_safe hj
  obtain ⟨middle,declared⟩:=ZeroFrame.declare_exists h.well .u64 "t" (.integer (integer64 t))
    (ZeroFrame.u64_storable t ht)
  have dt:=declare_storable (ZeroFrame.u64_storable t ht) (convert64 t ht) declared
  have lm:=ApplicationBirthFrame.locals_declare_old h.well h.locals
    (by intro i; cases i <;> decide) dt
  have rm:=ApplicationBirthFrame.array_declare_old h.well h.array dt
  have hi : start+j < length := by have hb:=h.bound; omega
  have tNamed : middle.environment.lookup "t"=some (scalarPointer before.nextObject .u64) := by
    rw [dt.environment]; rfl
  have readT : Eval context middle (.variable "t") (.integer (integer64 t)) middle :=
    .variable tNamed dt.slot.read
  have place : Place context middle (.index (.variable "a") (.variable "j"))
      (wordPointer object (start+j)) middle :=
    .index (.variable (lm.lookup Var.a) (lm.read Var.a))
      (.variable (lm.lookup Var.j) (lm.read Var.j)) (slice_pointer_add rm hi)
  have hm : t % base < 2^64 := lt_trans (Nat.mod_lt t (by norm_num [base])) (by norm_num [base])
  obtain ⟨after,stored,ra⟩:=word_store_with_rep rm hi hm
  have digit : Exec context middle digitStmt .normal after := by
    apply Exec.assign (value:=.integer (integer64 (t % base)))
      (Eval.paren (Eval.binaryLR readT
        (.literal (.integer 1000000000 "ULL") _ (.integer (integer64 base)) (by rfl))
        (by simp only [binary,binary64_mod t base ht (by norm_num [base]) (by norm_num [base]),Option.map_some]))) place
    exact stored
  have la:=ApplicationBirthFrame.locals_store_other lm (fun i=>(h.separate i).symm) stored
  have oldObj:=h.well.objectIds object _ h.array.2.1
  have ta:=ApplicationBirthFrame.slot_store_other dt.slot (by change before.nextObject≠object; omega) stored
  have wm:=wellScoped_declare h.well declared
  have frame:=ApplicationBirthFrame.Frame.trans
    (ApplicationBirthFrame.declare_frame before.nextObject (writes object li) h.well (le_refl _) declared)
    (ApplicationBirthFrame.store_frame before.nextObject (writes object li) wm
      (by rw [dt.nextObject]; omega) (Or.inl (by simp [writes,wordPointer])) stored)
  refine ⟨after,.cons (.declareSome (t_eval context h hj) declared) (.cons digit .nil),?_,la,ta,?_,frame⟩
  · simpa only [t,currentData_step] using ra
  · rw [(SourceLocals.store_frame stored).1]
    exact tNamed

theorem array_store_other {F : Type} {before after : State F} {object length : Nat}
    {data : Nat → Nat} {pointer : Pointer} {value : Value}
    (h : WordArrayRep before object length data) (different : object ≠ pointer.object)
    (stored : before.store pointer value=some after) : WordArrayRep after object length data := by
  obtain ⟨env,mode,scope,ns,no,outside⟩:=SourceLocals.store_frame stored
  exact ⟨mode.trans h.1,by rw [outside object different]; exact h.2.1,h.2.2⟩

#print axioms condition_eval
#print axioms t_eval
#print axioms digit_prefix_execution
end RH080Next.FFTPV.MultiplySmallSource
