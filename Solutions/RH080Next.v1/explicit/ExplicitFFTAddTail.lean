/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTAddBase
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.AddSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings
open FFT.Limbs
open IncrementSource (base)

def writes (i : Input) (li : Var → Nat) : List Nat:=[i.layout.object .out,li .j,li .carry]

theorem values_carry_update (i : Input) (j c d : Nat) :
    Function.update (values i j c) .carry (.integer (integer64 d))=values i j d := by
  funext v; cases v <;> rfl
theorem values_j_update (i : Input) (j c k : Nat) :
    Function.update (values i j c) .j (.integer (integer64 k))=values i k c := by
  funext v; cases v <;> rfl

theorem scalar_array_ne {F : Type} {state : State F} {id owner object length : Nat}
    {ctype : CType} {value : Value} {data : Nat → Nat}
    (slot : Slot state id owner ctype value) (array : WordArrayRep state object length data) : id≠object := by
  intro eq
  subst id
  have objects:=Option.some.inj (slot.object.symm.trans array.2.1)
  have storage:=congrArg Object.storage objects
  cases storage

theorem binary64_one_sub (q : Nat) (hq : q ≤ 1) :
    Integer.binary .sub (integer64 1) (integer64 q)=some (integer64 (1-q)) := by
  interval_cases q <;> rfl

theorem carry_eval {F : Type} (context : Context F) {state : State F} (sub : Bool) (t : Nat)
    (readT : Eval context state (.variable "t") (.integer (integer64 t)) state) (ht : t < 2*base) :
    Eval context state (carryExpr sub) (.integer (integer64 (nextCarry sub t))) state := by
  have t64 : t < 2^64:=lt_trans ht (by norm_num [base])
  have quotient : Eval context state (.paren (.binary .div (.variable "t")
      (.literal (.integer 1000000000 "ULL")))) (.integer (integer64 (t/base))) state:=
    .paren (.binaryLR readT (.literal (.integer 1000000000 "ULL") _ (.integer (integer64 base)) (by rfl))
      (by simp only [binary,binary64_div t base t64 (by norm_num [base]) (by norm_num [base]),Option.map_some]))
  cases sub with
  | false=>exact quotient
  | true=>
    have hq : t/base ≤ 1:=by have h: t/base < 2:=(Nat.div_lt_iff_lt_mul (by norm_num [base])).mpr (by omega); omega
    exact .paren (.binaryLR (.literal (.integer 1 "ULL") _ (.integer (integer64 1)) (by rfl)) quotient
      (by simp only [binary,binary64_one_sub (t/base) hq,Option.map_some,nextCarry,ite_true]))

/-- Common actual modulo/carry/counter tail of both source digit loops. Its
array proof supports out=a, out=b and disjoint slices in a shared object. -/
theorem digit_tail_execution {F : Type} (context : Context F) {before : State F} {input : Input}
    {sub swap : Bool} {owner j cutoff tId tOwner : Nat} {li : Var → Nat}
    (h : View before input sub swap owner li j) (hj : j < 5) (fresh : cutoff ≤ before.nextObject)
    (tSlot : Slot before tId tOwner .u64 (.integer (integer64
      (digitTotal sub (input.left swap j) (input.right swap j) (scan sub (input.left swap) (input.right swap) j).2))))
    (tNamed : before.environment.lookup "t"=some (scalarPointer tId .u64)) :
    ∃after,ExecList context before [digitStmt,carryStmt sub,advanceStmt] .normal after ∧
      View after input sub swap owner li (j+1) ∧
      ApplicationBirthFrame.Frame cutoff before after (writes input li) := by
  let t:=digitTotal sub (input.left swap j) (input.right swap j) (scan sub (input.left swap) (input.right swap) j).2
  have bounds:=digitTotal_bounds sub _ _ _ (input.left_bound swap j hj) (input.right_bound swap j hj) h.carry_bound
  have ht : t < 2*base:=bounds.1
  have ht64 : t < 2^64:=lt_trans ht (by norm_num [base])
  have next64 : nextCarry sub t < 2^64:=by have hc : nextCarry sub t ≤ 1:=bounds.2; omega
  obtain ⟨middle,stored,am⟩:=h.arrays.store_digit hj
  have hi : input.layout.start .out+j < input.layout.length (input.layout.object .out):=by have hb:=input.layout.bound .out; omega
  have readT : Eval context before (.variable "t") (.integer (integer64 t)) before:=.variable tNamed tSlot.read
  have storeRun : Exec context before digitStmt .normal middle := by
    apply Exec.assign (value:=.integer (integer64 (t%base)))
      (Eval.paren (.binaryLR readT (.literal (.integer 1000000000 "ULL") _ (.integer (integer64 base)) (by rfl))
        (by simp only [binary,binary64_mod t base ht64 (by norm_num [base]) (by norm_num [base]),Option.map_some])))
      (Place.index (.variable (h.locals.lookup Var.out) (h.locals.read Var.out))
        (.variable (h.locals.lookup Var.j) (h.locals.read Var.j)) (slice_pointer_add (h.arrays .out) hi))
    exact stored
  have lm:=ApplicationBirthFrame.locals_store_other h.locals (fun v=>(h.separate .out v).symm) stored
  have tm:=ApplicationBirthFrame.slot_store_other tSlot (scalar_array_ne tSlot (h.arrays .out)) stored
  have named : middle.environment.lookup "t"=some (scalarPointer tId .u64):=by rw [(SourceLocals.store_frame stored).1]; exact tNamed
  have fm:=ApplicationBirthFrame.store_frame cutoff (writes input li) h.well fresh
    (Or.inl (by simp [writes,wordPointer])) stored
  have storable:=ZeroFrame.u64_storable (nextCarry sub t) next64
  obtain ⟨carried,storeCarry⟩:=IncrementSource.slot_store_exists (lm.slots Var.carry) (.integer (integer64 (nextCarry sub t))) storable
  have carryRun : Exec context middle (carryStmt sub) .normal carried := by
    exact .assign (carry_eval context sub t (.variable named tm.read) ht) (Place.variable (lm.lookup Var.carry)) storeCarry
  have lc : Locals carried name type li owner (values input j (nextCarry sub t)):=by
    simpa only [values_carry_update] using lm.store Var.carry _ storable storeCarry
  have ac:=am.store_other (fun r=>h.separate r Var.carry) storeCarry
  have fc:=ApplicationBirthFrame.store_frame cutoff (writes input li) fm.well fm.fresh
    (Or.inl (by simp [writes,scalarPointer])) storeCarry
  have j64 : j < 2^64:=by omega
  have j1 : j+1 < 2^64:=by omega
  have sj:=ZeroFrame.u64_storable (j+1) j1
  obtain ⟨after,storeJ⟩:=IncrementSource.slot_store_exists (lc.slots Var.j) (.integer (integer64 (j+1))) sj
  have advanceRun : Exec context carried advanceStmt .normal after := by
    apply Exec.assign (value:=.integer (integer64 (j+1)))
      (Eval.paren (.binaryLR (.variable (lc.lookup Var.j) (lc.read Var.j))
        (.literal (.integer 1 "ULL") _ (.integer (integer64 1)) (by rfl))
        (by simp only [values,binary,binary64_add j 1 j64 (by norm_num) j1,Option.map_some])))
      (Place.variable (lc.lookup Var.j))
    exact storeJ
  have la : Locals after name type li owner (values input (j+1) (nextCarry sub t)):=by
    simpa only [values_j_update] using lc.store Var.j _ sj storeJ
  have aa:=ac.store_other (fun r=>h.separate r Var.j) storeJ
  have fj:=ApplicationBirthFrame.store_frame cutoff (writes input li) fc.well fc.fresh
    (Or.inl (by simp [writes,scalarPointer])) storeJ
  have whole:=fm.trans (fc.trans fj)
  have la' : Locals after name type li owner (values input (j+1) (scan sub (input.left swap) (input.right swap) (j+1)).2):=by
    simpa only [scan_step] using la
  exact ⟨after,.cons storeRun (.cons carryRun (.cons advanceRun .nil)),⟨aa,la',h.separate,by omega,whole.well⟩,whole⟩

#print axioms scalar_array_ne
#print axioms carry_eval
#print axioms digit_tail_execution
end RH080Next.FFTPV.AddSource
