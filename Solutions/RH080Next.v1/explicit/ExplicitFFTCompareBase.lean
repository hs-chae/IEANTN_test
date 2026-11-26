/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTZeroParameters
import FFTWordSlices
import FFTPureDeterminism
import FFTLimbAddition

set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.CompareSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings

inductive Var where | a | b | j deriving DecidableEq
def name : Var → String | .a=>"a" | .b=>"b" | .j=>"j"
def type : Var → CType | .a | .b => .pointer .u64 | .j => .u64
def values (aObject aStart bObject bStart j : Nat) : Var → Value
  | .a => .pointer (wordPointer aObject aStart)
  | .b => .pointer (wordPointer bObject bStart)
  | .j => .integer (integer64 j)
def ids (base : Nat) : Var → Nat | .a=>base | .b=>base+1 | .j=>base+2

def condition : Expr := .binary .gt (.variable "j") (.literal (.integer 0 "ULL"))
def decrement : Stmt := .assign (.variable "j")
  (.paren (.binary .sub (.variable "j") (.literal (.integer 1 "ULL"))))
def index (v : Var) : Expr := .index (.variable (name v)) (.variable "j")
def comparison (op : Binary) : Expr := .binary op (index .a) (index .b)
def returnStmt (n : Nat) : Stmt := .returnValue (some (.literal (.integer n "ULL")))
def branch (op : Binary) (n : Nat) : Stmt := .ite (comparison op) (.block [returnStmt n]) none
def loopBody : Stmt := .block [decrement,branch .gt 2,branch .lt 0]
def loop : Stmt := .whileLoop condition loopBody

theorem actual_body : magnitude_compare_ast.body = .block [
    .declare .u64 "j" (some (.literal (.integer 5 "ULL"))),loop,returnStmt 1] := by rfl

structure View {F : Type} (state : State F)
    (aObject aLength aStart bObject bLength bStart owner : Nat)
    (localsIds : Var → Nat) (a b : Nat → Nat) (j : Nat) : Prop where
  left : WordArrayRep state aObject aLength a
  right : WordArrayRep state bObject bLength b
  locals : Locals state name type localsIds owner (values aObject aStart bObject bStart j)
  separate : ∀v,aObject≠localsIds v ∧ bObject≠localsIds v
  leftBound : aStart+5≤aLength
  rightBound : bStart+5≤bLength
  active : j≤5
  well : WellScoped state

theorem View.enter {F : Type} {state : State F}
    {ao al ast bo bl bst owner j : Nat} {li : Var → Nat} {a b : Nat → Nat}
    (h : View state ao al ast bo bl bst owner li a b j) :
    View state.enterScope ao al ast bo bl bst owner li a b j :=
  ⟨h.left,h.right,h.locals.enter,h.separate,h.leftBound,h.rightBound,h.active,wellScoped_enter h.well⟩

theorem pointer_storable (object start : Nat) :
    Storable (.pointer .u64) (.pointer (wordPointer object start)) := by
  have hb : (Value.pointer (wordPointer object start)).byteSize=8 := stored_pointer_width _
  exact ⟨by rw [hb]; rfl,by rw [hb]; decide,by rfl⟩

private theorem slot_declare_other {F : Type} {before after : State F}
    {id owner : Nat} {oldtype newtype : CType} {oldvalue newvalue : Value} {cname : String}
    (h : Slot before id owner oldtype oldvalue)
    (d : Declaration before after cname newtype newvalue)
    (different : id≠before.nextObject) : Slot after id owner oldtype oldvalue :=
  ⟨h.storable,by rw [d.outside id different]; exact h.object⟩

/-- Both actual pointer parameters and j=5 are allocated from the real caller
state. Neither parameter binding nor application initialization is assumed. -/
theorem initialize_parameters {F : Type} {entry : State F}
    {ao al ast bo bl bst : Nat} {a b : Nat → Nat}
    (well : WellScoped entry) (emptyEnv : entry.environment=[])
    (left : WordArrayRep entry ao al a) (right : WordArrayRep entry bo bl b)
    (leftBound : ast+5≤al) (rightBound : bst+5≤bl) :
    ∃sa sb sj,
      entry.declare (.pointer .u64) "a" (some (.pointer (wordPointer ao ast)))=some sa ∧
      sa.declare (.pointer .u64) "b" (some (.pointer (wordPointer bo bst)))=some sb ∧
      sb.declare .u64 "j" (some (.integer (integer64 5)))=some sj ∧
      View sj ao al ast bo bl bst entry.scope (ids entry.nextObject) a b 5 := by
  obtain ⟨sa,da⟩ := ZeroFrame.declare_exists well _ "a" _ (pointer_storable ao ast)
  have wa := wellScoped_declare well da
  obtain ⟨sb,db⟩ := ZeroFrame.declare_exists wa _ "b" _ (pointer_storable bo bst)
  have wb := wellScoped_declare wa db
  obtain ⟨sj,dj⟩ := ZeroFrame.declare_exists wb _ "j" _ (ZeroFrame.u64_storable 5 (by norm_num))
  have ia := declare_storable (pointer_storable ao ast) (pointer_storable ao ast).converted da
  have ib := declare_storable (pointer_storable bo bst) (pointer_storable bo bst).converted db
  have ij := declare_storable (ZeroFrame.u64_storable 5 (by norm_num)) (ZeroFrame.u64_storable 5 (by norm_num)).converted dj
  have oa := ia.nextObject
  have ob := ib.nextObject
  have sca := ia.scope
  have scb := ib.scope
  have oldA : ao<entry.nextObject := well.objectIds _ _ left.2.1
  have oldB : bo<entry.nextObject := well.objectIds _ _ right.2.1
  have lm : Locals sj name type (ids entry.nextObject) entry.scope (values ao ast bo bst 5) := by
    constructor
    · intro v
      cases v <;> simp [ids,name,type,ij.environment,ib.environment,ia.environment,
        emptyEnv,oa,ob,scalarPointer,List.lookup]
    · intro v
      cases v with
      | a =>
        have h1 := slot_declare_other ia.slot ib (by omega)
        have h2 := slot_declare_other h1 ij (by omega)
        simpa only [ids,type,values] using h2
      | b =>
        have h1 := slot_declare_other ib.slot ij (by omega)
        simpa only [ids,type,values,oa,sca] using h1
      | j => simpa only [ids,type,values,oa,ob,sca,scb] using ij.slot
    · intro v w h
      cases v <;> cases w <;> simp_all [ids] <;> omega
    · rw [ij.nextScope,ib.nextScope,ia.nextScope]
      exact well.current
  have host : sj.mode=.host := ij.mode.trans (ib.mode.trans (ia.mode.trans left.1))
  refine ⟨sa,sb,sj,da,db,dj,⟨host,?_,left.2.2⟩,⟨host,?_,right.2.2⟩,lm,?_,leftBound,rightBound,by norm_num,wellScoped_declare wb dj⟩
  · rw [ij.outside ao (by omega),ib.outside ao (by omega),ia.outside ao (by omega)]
    exact left.2.1
  · rw [ij.outside bo (by omega),ib.outside bo (by omega),ia.outside bo (by omega)]
    exact right.2.1
  · intro v
    cases v <;> simp only [ids] <;> omega

private theorem slot_store_exists {F : Type} {state : State F} {id owner : Nat}
    {ctype : CType} {oldValue : Value} (h : Slot state id owner ctype oldValue)
    (v : Value) (hv : Storable ctype v) : ∃after,state.store (scalarPointer id ctype) v=some after := by
  obtain ⟨oldType,present⟩ := h
  have hsame : oldValue.byteSize=v.byteSize := Option.some.inj (oldType.typeWidth.symm.trans hv.typeWidth)
  rw [hsame] at present
  simp [State.store,scalarPointer,present,scalarObject,State.accessible,hv.typeWidth,hv.converted]

theorem binary64_sub_one (j : Nat) (hj : j+1<2^64) :
    Integer.binary .sub (integer64 (j+1)) (integer64 1)=some (integer64 j) := by
  change Integer.checked .u64 ((Integer.cast .u64 (((j+1:Nat):Int))).toInt-
    (Integer.cast .u64 (1:Int)).toInt)=some (integer64 j)
  have h1 : Integer.cast .u64 (1:Int)=integer64 1 := by decide
  rw [cast64_exact (j+1) hj,h1,integer64_toInt,integer64_toInt]
  have he : ((j+1:Nat):Int)-(1:Int)=(j:Int) := by omega
  norm_num only [Nat.cast_one]
  rw [he]
  change some (Integer.cast .u64 (j:Int))=some (integer64 j)
  rw [cast64_exact j (by omega)]

/-- The actual decrement is safe unsigned subtraction, updates j alone and
preserves both arbitrary input slices, including aliases. -/
theorem decrement_execution {F : Type} (context : Context F) {before : State F}
    {ao al ast bo bl bst owner j : Nat} {li : Var → Nat} {a b : Nat → Nat}
    (h : View before ao al ast bo bl bst owner li a b (j+1)) :
    ∃after,Exec context before decrement .normal after ∧ View after ao al ast bo bl bst owner li a b j := by
  have hj : j+1<2^64 := by have hh:=h.active; omega
  obtain ⟨after,written⟩ := slot_store_exists (h.locals.slots Var.j)
    (.integer (integer64 j)) (ZeroFrame.u64_storable j (by omega))
  have run : Exec context before decrement .normal after := by
    apply Exec.assign (value:=.integer (integer64 j))
      (Eval.paren (Eval.binaryLR (.variable (h.locals.lookup Var.j) (h.locals.read Var.j))
        (.literal (.integer 1 "ULL") _ (.integer (integer64 1)) (by rfl))
        (by simp only [values,binary,binary64_sub_one j hj,Option.map_some])))
      (.variable (h.locals.lookup Var.j))
    exact written
  have la := h.locals.store Var.j (.integer (integer64 j)) (ZeroFrame.u64_storable j (by omega)) written
  have hv : Function.update (values ao ast bo bst (j+1)) Var.j (.integer (integer64 j))=values ao ast bo bst j := by
    funext v
    cases v <;> simp [values,Function.update]
  rw [hv] at la
  obtain ⟨_,mode,_,_,_,outside⟩ := store_frame written
  have ra : WordArrayRep after ao al a :=
    ⟨mode.trans h.left.1,(outside ao (h.separate Var.j).1).trans h.left.2.1,h.left.2.2⟩
  have rb : WordArrayRep after bo bl b :=
    ⟨mode.trans h.right.1,(outside bo (h.separate Var.j).2).trans h.right.2.1,h.right.2.2⟩
  exact ⟨after,run,ra,rb,la,h.separate,h.leftBound,h.rightBound,by have hh:=h.active; omega,wellScoped_store h.well written⟩

#print axioms initialize_parameters
#print axioms decrement_execution
end RH080Next.FFTPV.CompareSource
