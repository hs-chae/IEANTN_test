/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitApplicationBirthFrame
import ExplicitFFTCompareDeterminism
import FFTWordDivision
import FFTLimbIncrement
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.IncrementSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings
open FFT.Limbs

def base : Nat := 1000000000

def currentData (old : Nat → Nat) (start j i : Nat) : Nat :=
  if start ≤ i ∧ i < start+j then (incrementDigits base (fun k=>old (start+k)) j).1 (i-start) else old i

theorem currentData_zero (old : Nat → Nat) (start : Nat) : currentData old start 0=old := by
  funext i
  simp [currentData]

theorem currentData_unread (old : Nat → Nat) (start j : Nat) :
    currentData old start j (start+j)=old (start+j) := by simp [currentData]

theorem currentData_step (old : Nat → Nat) (start j : Nat) :
    Function.update (currentData old start j) (start+j)
      ((old (start+j)+(incrementDigits base (fun k=>old (start+k)) j).2)%base)=currentData old start (j+1) := by
  funext i
  by_cases he : i=start+j
  · subst i
    simp [currentData,incrementDigits]
  · by_cases hi : start ≤ i ∧ i < start+j
    · have hne : i-start≠j := by omega
      simp [currentData,Function.update_of_ne he,hi,
        show start ≤ i ∧ i < start+(j+1) by omega,incrementDigits,Function.update_of_ne hne]
    · simp [currentData,Function.update_of_ne he,hi,
        show ¬(start ≤ i ∧ i < start+(j+1)) by omega]

inductive Var where | a | n | j | carry deriving DecidableEq
def name : Var → String | .a=>"a" | .n=>"n" | .j=>"j" | .carry=>"carry"
def type : Var → CType | .a=>.pointer .u64 | _=>.u64
def values (object start n j carry : Nat) : Var → Value
  | .a=>.pointer (wordPointer object start)
  | .n=>.integer (integer64 n)
  | .j=>.integer (integer64 j)
  | .carry=>.integer (integer64 carry)
def ids (first : Nat) : Var → Nat | .a=>first | .n=>first+1 | .j=>first+2 | .carry=>first+3

def condition : Expr := .binary .lt (.variable "j") (.variable "n")
def tExpr : Expr := .paren (.binary .add (.index (.variable "a") (.variable "j")) (.variable "carry"))
def digitStmt : Stmt := .assign (.index (.variable "a") (.variable "j"))
  (.paren (.binary .mod (.variable "t") (.literal (.integer 1000000000 "ULL"))))
def carryStmt : Stmt := .assign (.variable "carry")
  (.paren (.binary .div (.variable "t") (.literal (.integer 1000000000 "ULL"))))
def advanceStmt : Stmt := .assign (.variable "j")
  (.paren (.binary .add (.variable "j") (.literal (.integer 1 "ULL"))))
def loopBody : Stmt := .block [.declare .u64 "t" (some tExpr),digitStmt,carryStmt,advanceStmt]
def loop : Stmt := .whileLoop condition loopBody

theorem actual_body : increment_words_ast.body=.block [
    .declare .u64 "j" (some (.literal (.integer 0 "ULL"))),
    .declare .u64 "carry" (some (.literal (.integer 1 "ULL"))),loop,
    .returnValue (some (.variable "carry"))] := by rfl

structure View {F : Type} (state : State F) (object length start n owner : Nat)
    (li : Var → Nat) (old : Nat → Nat) (j : Nat) : Prop where
  array : WordArrayRep state object length (currentData old start j)
  locals : Locals state name type li owner
    (values object start n j (incrementDigits base (fun k=>old (start+k)) j).2)
  separate : ∀v,object≠li v
  bound : start+n ≤ length
  small : n ≤ 6
  active : j ≤ n
  digits : ∀i < n,old (start+i) < base
  well : WellScoped state

theorem View.enter {F : Type} {state : State F} {object length start n owner j : Nat}
    {li : Var → Nat} {old : Nat → Nat} (h : View state object length start n owner li old j) :
    View state.enterScope object length start n owner li old j :=
  ⟨h.array,h.locals.enter,h.separate,h.bound,h.small,h.active,h.digits,wellScoped_enter h.well⟩

private theorem pointer_storable (object start : Nat) :
    Storable (.pointer .u64) (.pointer (wordPointer object start)) := by
  have hb : (Value.pointer (wordPointer object start)).byteSize=8 := stored_pointer_width _
  exact ⟨by rw [hb]; rfl,by rw [hb]; decide,by rfl⟩

/-- The actual pointer/length parameters and both persistent locals are born
at their true function scope, with no pre-existing application bindings. -/
theorem initialize_parameters {F : Type} {entry : State F} {object length start n : Nat}
    {old : Nat → Nat} (well : WellScoped entry) (empty : entry.environment=[])
    (rep : WordArrayRep entry object length old) (bound : start+n ≤ length) (small : n ≤ 6)
    (digits : ∀i < n,old (start+i) < base) :
    ∃sa sn sj sc,
      entry.declare (.pointer .u64) "a" (some (.pointer (wordPointer object start)))=some sa ∧
      sa.declare .u64 "n" (some (.integer (integer64 n)))=some sn ∧
      sn.declare .u64 "j" (some (.integer (integer64 0)))=some sj ∧
      sj.declare .u64 "carry" (some (.integer (integer64 1)))=some sc ∧
      View sc object length start n entry.scope (ids entry.nextObject) old 0 := by
  obtain ⟨sa,da⟩ := ZeroFrame.declare_exists well _ "a" _ (pointer_storable object start)
  have wa := wellScoped_declare well da
  obtain ⟨sn,dn⟩ := ZeroFrame.declare_exists wa _ "n" _ (ZeroFrame.u64_storable n (by omega))
  have wn := wellScoped_declare wa dn
  obtain ⟨sj,dj⟩ := ZeroFrame.declare_exists wn _ "j" _ (ZeroFrame.u64_storable 0 (by norm_num))
  have wj := wellScoped_declare wn dj
  obtain ⟨sc,dc⟩ := ZeroFrame.declare_exists wj _ "carry" _ (ZeroFrame.u64_storable 1 (by norm_num))
  have ia := declare_storable (pointer_storable object start) (pointer_storable object start).converted da
  have inn := declare_storable (ZeroFrame.u64_storable n (by omega)) (convert64 n (by omega)) dn
  have ij := declare_storable (ZeroFrame.u64_storable 0 (by norm_num)) (convert64 0 (by norm_num)) dj
  have ic := declare_storable (ZeroFrame.u64_storable 1 (by norm_num)) (convert64 1 (by norm_num)) dc
  have oa:=ia.nextObject
  have on:=inn.nextObject
  have oj:=ij.nextObject
  have saScope:=ia.scope
  have snScope:=inn.scope
  have sjScope:=ij.scope
  have oldObject : object < entry.nextObject := well.objectIds _ _ rep.2.1
  have lm : Locals sc name type (ids entry.nextObject) entry.scope (values object start n 0 1) := by
    constructor
    · intro v
      cases v  <;> simp [ids,name,type,ic.environment,ij.environment,inn.environment,ia.environment,
        empty,oa,on,oj,scalarPointer,List.lookup]
    · intro v
      cases v with
      | a =>
        have h1:=ApplicationBirthFrame.slot_declare_old wa ia.slot inn
        have h2:=ApplicationBirthFrame.slot_declare_old wn h1 ij
        have h3:=ApplicationBirthFrame.slot_declare_old wj h2 ic
        simpa only [ids,type,values] using h3
      | n =>
        have h1:=ApplicationBirthFrame.slot_declare_old wn inn.slot ij
        have h2:=ApplicationBirthFrame.slot_declare_old wj h1 ic
        simpa only [ids,type,values,oa,saScope] using h2
      | j =>
        have h1:=ApplicationBirthFrame.slot_declare_old wj ij.slot ic
        simpa only [ids,type,values,oa,on,saScope,snScope] using h1
      | carry => simpa only [ids,type,values,oa,on,oj,saScope,snScope,sjScope] using ic.slot
    · intro v w he
      cases v  <;> cases w  <;> simp_all [ids]  <;> omega
    · rw [ic.nextScope,ij.nextScope,inn.nextScope,ia.nextScope]
      exact well.current
  have host : sc.mode=.host := ic.mode.trans (ij.mode.trans (inn.mode.trans (ia.mode.trans rep.1)))
  have array : WordArrayRep sc object length old := by
    refine ⟨host,?_,rep.2.2⟩
    rw [ic.outside object (by omega),ij.outside object (by omega),inn.outside object (by omega),ia.outside object (by omega)]
    exact rep.2.1
  refine ⟨sa,sn,sj,sc,da,dn,dj,dc,?_,?_,?_,bound,small,by omega,digits,wellScoped_declare wj dc⟩
  · simpa only [currentData_zero] using array
  · simpa only [incrementDigits] using lm
  · intro v
    cases v  <;> simp only [ids]  <;> omega

theorem slot_store_exists {F : Type} {state : State F} {id owner : Nat}
    {ctype : CType} {oldValue : Value} (h : Slot state id owner ctype oldValue)
    (v : Value) (hv : Storable ctype v) : ∃after,state.store (scalarPointer id ctype) v=some after := by
  obtain ⟨oldType,present⟩ := h
  have same : oldValue.byteSize=v.byteSize := Option.some.inj (oldType.typeWidth.symm.trans hv.typeWidth)
  rw [same] at present
  simp [State.store,scalarPointer,present,scalarObject,State.accessible,hv.typeWidth,hv.converted]

#print axioms currentData_step
#print axioms initialize_parameters
end RH080Next.FFTPV.IncrementSource
