/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTMainAllocationBirth
import FFTRecursiveIndexExpressions
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.MainAllocation
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings ApplicationBirthFrame

inductive Role where | data | twiddle | work | output deriving DecidableEq

def name : Role → String
  | .data=>"data" | .twiddle=>"twiddle" | .work=>"work" | .output=>"output"
def length (n : Nat) : Role → Nat
  | .data | .output=>n*12 | .twiddle=>(n/2)*12 | .work=>512

def countExpr : Role → Expr
  | .data | .output=>RecursiveSource.mulExpr (.variable "n") (RecursiveSource.literal 12)
  | .twiddle=>RecursiveSource.mulExpr
      (.paren (.binary .div (.variable "n") (RecursiveSource.literal 2))) (RecursiveSource.literal 12)
  | .work=>RecursiveSource.literal 512

def statement (role : Role) : Stmt := .declare (.pointer .u64) (name role) (some (callocExpr (countExpr role)))

theorem name_injective : Function.Injective name := by
  intro a b eq
  cases a <;> cases b <;> simp_all [name]

/-- Only actually allocated byte buffers and actually declared pointer slots
are present. It contains no typed-word contents or desired numerical output. -/
structure View {F : Type} (state : State F) (n nId owner : Nat) (roles : List Role)
    (objects ids : Role → Nat) : Prop where
  nLookup : state.environment.lookup "n"=some (scalarPointer nId .u64)
  nSlot : Slot state nId owner .u64 (.integer (integer64 n))
  lookup : ∀r∈roles,state.environment.lookup (name r)=some (scalarPointer (ids r) (.pointer .u64))
  slots : ∀r∈roles,Slot state (ids r) owner (.pointer .u64) (.pointer (wordPointer (objects r) 0))
  raw : ∀r∈roles,state.objects (objects r)=some (zeroPrefixObject (length n r) 0)
  differentObjects : ∀r∈roles,∀s∈roles,objects r=objects s → r=s
  differentSlots : ∀r∈roles,∀s∈roles,ids r=ids s → r=s
  nSeparate : ∀r∈roles,nId≠ids r
  well : WellScoped state
  host : state.mode=.host
  scope : state.scope=owner

theorem View.initial {F : Type} {state : State F} {n nId owner : Nat}
    (lookup : state.environment.lookup "n"=some (scalarPointer nId .u64))
    (slot : Slot state nId owner .u64 (.integer (integer64 n)))
    (well : WellScoped state) (host : state.mode=.host) (scope : state.scope=owner) :
    View state n nId owner [] (fun _=>0) (fun _=>0) := by
  refine ⟨lookup,slot,?_,?_,?_,?_,?_,?_,well,host,scope⟩ <;> simp

theorem View.count_eval {F : Type} (context : Context F) {state : State F}
    {n nId owner : Nat} {roles : List Role} {objects ids : Role → Nat}
    (h : View state n nId owner roles objects ids) (small : n≤2^24) (r : Role) :
    Eval context state (countExpr r) (.integer (integer64 (length n r))) state := by
  have fit : n<2^64 := by omega
  have nEval : Eval context state (.variable "n") (.integer (integer64 n)) state :=
    .variable h.nLookup h.nSlot.read
  have lit12 : Eval context state (RecursiveSource.literal 12) (.integer (integer64 12)) state :=
    .literal (.integer 12 "ULL") _ (.integer (integer64 12)) (by rfl)
  have productFit : n*12<2^64 := by omega
  cases r with
  | data => exact RecursiveSource.mul_expr_eval context nEval lit12 fit (by norm_num) productFit
  | output => exact RecursiveSource.mul_expr_eval context nEval lit12 fit (by norm_num) productFit
  | work => exact .literal (.integer 512 "ULL") _ (.integer (integer64 512)) (by rfl)
  | twiddle =>
    have half:=RecursiveSource.div_expr_eval context nEval
      (Eval.literal (.integer 2 "ULL") _ (.integer (integer64 2)) (by rfl)) fit (by norm_num) (by decide)
    exact RecursiveSource.mul_expr_eval context half lit12 (by omega) (by norm_num) (by omega)

theorem length_bytes_fit {n : Nat} (small : n≤2^24) (r : Role) : length n r*8<2^64 := by
  cases r <;> simp only [length] <;> omega

private theorem keep_slot {F : Type} {before after : State F} {id owner : Nat}
    {ctype : CType} {value : Value} (well : WellScoped before)
    (slot : Slot before id owner ctype value) (frame : Frame before.nextObject before after []) :
    Slot after id owner ctype value :=
  ⟨slot.storable,(frame.outside id (well.objectIds _ _ slot.object) (by simp)).trans slot.object⟩

/-- Each real source declaration extends the current view with the fresh
allocator object, preserving all previously declared slots and raw buffers. -/
theorem View.birth {F : Type} (context : Context F) {before : State F}
    {n nId owner : Nat} {roles : List Role} {objects ids : Role → Nat} (next : Role)
    (h : View before n nId owner roles objects ids) (small : n≤2^24)
    (notBorn : next∉roles) (absent : findFunction context.program "calloc"=none) (memory : HasMemory context) :
    ∃after pointerId,Exec context before (statement next) .normal after ∧
      View after n nId owner (next::roles) (Function.update objects next before.nextObject)
        (Function.update ids next pointerId) ∧ Frame before.nextObject before after [] := by
  obtain ⟨after,pointerId,run,raw,lookup,slot,frame,scope,environment,pointerLower,pointerUpper⟩:=
    calloc_pointer_birth context (name next) absent memory h.well h.host (length_bytes_fit small next) (h.count_eval context small next)
  have oldNe (r : Role) (member : r∈roles) : r≠next := by intro eq;exact notBorn (eq ▸ member)
  have objectBound (r : Role) (member : r∈roles) : objects r<before.nextObject := h.well.objectIds _ _ (h.raw r member)
  have slotBound (r : Role) (member : r∈roles) : ids r<before.nextObject := h.well.objectIds _ _ (h.slots r member).object
  have nBound : nId<before.nextObject := h.well.objectIds _ _ h.nSlot.object
  refine ⟨after,pointerId,run,⟨?_,keep_slot h.well h.nSlot frame,?_,?_,?_,?_,?_,?_,frame.well,
    frame.mode.trans h.host,scope.trans h.scope⟩,frame⟩
  · have ne : name next≠"n" := by cases next <;> decide
    rw [environment]
    simpa [List.lookup,show ("n"==name next)=false by simp [Ne.symm ne]] using h.nLookup
  · intro r member
    rcases List.mem_cons.mp member with eq | old
    · subst r
      simpa using lookup
    · have ne:=oldNe r old
      have names : name r≠name next := by intro eq;exact ne (name_injective eq)
      rw [Function.update_of_ne ne,environment]
      simpa [List.lookup,show (name r==name next)=false by simp [names]] using h.lookup r old
  · intro r member
    rcases List.mem_cons.mp member with eq | old
    · subst r
      simpa [h.scope] using slot
    · have ne:=oldNe r old
      rw [Function.update_of_ne ne,Function.update_of_ne ne]
      exact keep_slot h.well (h.slots r old) frame
  · intro r member
    rcases List.mem_cons.mp member with eq | old
    · subst r
      simpa using raw
    · have ne:=oldNe r old
      rw [Function.update_of_ne ne]
      exact (frame.outside _ (objectBound r old) (by simp)).trans (h.raw r old)
  · intro r rm s sm same
    rcases List.mem_cons.mp rm with rnew | rold
    · subst r
      rcases List.mem_cons.mp sm with snew | sold
      · exact snew.symm
      · have ne:=oldNe s sold
        have bound:=objectBound s sold
        simp only [Function.update_self,Function.update_of_ne ne] at same
        omega
    · rcases List.mem_cons.mp sm with snew | sold
      · subst s
        have ne:=oldNe r rold
        have bound:=objectBound r rold
        simp only [Function.update_self,Function.update_of_ne ne] at same
        omega
      · rw [Function.update_of_ne (oldNe r rold),Function.update_of_ne (oldNe s sold)] at same
        exact h.differentObjects r rold s sold same
  · intro r rm s sm same
    rcases List.mem_cons.mp rm with rnew | rold
    · subst r
      rcases List.mem_cons.mp sm with snew | sold
      · exact snew.symm
      · have ne:=oldNe s sold
        have bound:=slotBound s sold
        simp only [Function.update_self,Function.update_of_ne ne] at same
        omega
    · rcases List.mem_cons.mp sm with snew | sold
      · subst s
        have ne:=oldNe r rold
        have bound:=slotBound r rold
        simp only [Function.update_self,Function.update_of_ne ne] at same
        omega
      · rw [Function.update_of_ne (oldNe r rold),Function.update_of_ne (oldNe s sold)] at same
        exact h.differentSlots r rold s sold same
  · intro r member
    rcases List.mem_cons.mp member with eq | old
    · subst r
      simp only [Function.update_self]
      omega
    · rw [Function.update_of_ne (oldNe r old)]
      exact h.nSeparate r old

#print axioms View.initial
#print axioms View.count_eval
#print axioms View.birth
end RH080Next.FFTPV.MainAllocation
