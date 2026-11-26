/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTMultiplySmallModel
import FFTWordDivision
import FFTCopyParameters
import ExplicitApplicationBirthFrame
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.MultiplySmallSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings
open FFT.Limbs

inductive Var where | a | n | m | j | carry deriving DecidableEq

def name : Var→String | .a=>"a" | .n=>"n" | .m=>"m" | .j=>"j" | .carry=>"carry"
def type : Var→CType | .a=>.pointer .u64 | _=>.u64
def values (object start n factor j carry : Nat) : Var→Value
  | .a=>.pointer (wordPointer object start) | .n=>.integer (integer64 n)
  | .m=>.integer (integer64 factor) | .j=>.integer (integer64 j) | .carry=>.integer (integer64 carry)
def ids (first : Nat) : Var→Nat | .a=>first | .n=>first+1 | .m=>first+2 | .j=>first+3 | .carry=>first+4

def condition : Expr:=.binary .lt (.variable "j") (.variable "n")
def tExpr : Expr:=.paren (.binary .add
  (.paren (.binary .mul (.index (.variable "a") (.variable "j")) (.variable "m"))) (.variable "carry"))
def digitStmt : Stmt:=.assign (.index (.variable "a") (.variable "j"))
  (.paren (.binary .mod (.variable "t") (.literal (.integer 1000000000 "ULL"))))
def carryStmt : Stmt:=.assign (.variable "carry")
  (.paren (.binary .div (.variable "t") (.literal (.integer 1000000000 "ULL"))))
def advanceStmt : Stmt:=.assign (.variable "j")
  (.paren (.binary .add (.variable "j") (.literal (.integer 1 "ULL"))))
def loopBody : Stmt:=.block [.declare .u64 "t" (some tExpr),digitStmt,carryStmt,advanceStmt]
def loop : Stmt:=.whileLoop condition loopBody

theorem actual_body : multiply_small_ast.body=.block [
    .declare .u64 "j" (some (.literal (.integer 0 "ULL"))),
    .declare .u64 "carry" (some (.literal (.integer 0 "ULL"))),loop,
    .returnValue (some (.variable "carry"))]:=by rfl

structure View {F : Type} (state : State F) (object length start n factor owner : Nat)
    (li : Var→Nat) (old : Nat→Nat) (j : Nat) : Prop where
  array : WordArrayRep state object length (currentData old start factor j)
  locals : Locals state name type li owner (values object start n factor j (scaledRow old start factor j).2)
  separate : ∀v,object≠li v
  bound : start+n≤length
  small : n≤6
  active : j≤n
  digits : ∀i,i<n → old (start+i)<base
  factorSmall : factor<base
  well : WellScoped state

theorem View.enter {F : Type} {state : State F} {object length start n factor owner j : Nat}
    {li : Var→Nat} {old : Nat→Nat} (h : View state object length start n factor owner li old j) :
    View state.enterScope object length start n factor owner li old j:=
  ⟨h.array,h.locals.enter,h.separate,h.bound,h.small,h.active,h.digits,h.factorSmall,wellScoped_enter h.well⟩

/-- The actual three parameters and two persistent locals are initialized
through their real C declarations at the function scope. -/
theorem initialize_parameters {F : Type} {entry : State F} {object length start n factor : Nat}
    {old : Nat→Nat} (well : WellScoped entry) (empty : entry.environment=[])
    (rep : WordArrayRep entry object length old) (bound : start+n≤length) (small : n≤6)
    (digits : ∀i,i<n → old (start+i)<base) (factorSmall : factor<base) :
    ∃sa sn sm sj sc,
      entry.declare (.pointer .u64) "a" (some (.pointer (wordPointer object start)))=some sa ∧
      sa.declare .u64 "n" (some (.integer (integer64 n)))=some sn ∧
      sn.declare .u64 "m" (some (.integer (integer64 factor)))=some sm ∧
      sm.declare .u64 "j" (some (.integer (integer64 0)))=some sj ∧
      sj.declare .u64 "carry" (some (.integer (integer64 0)))=some sc ∧
      View sc object length start n factor entry.scope (ids entry.nextObject) old 0:=by
  have ff : factor<2^64:=by dsimp [base] at factorSmall;omega
  obtain ⟨sa,da⟩:=ZeroFrame.declare_exists well _ "a" _ (CopyLoop.pointer_storable object start)
  have wa:=wellScoped_declare well da
  obtain ⟨sn,dn⟩:=ZeroFrame.declare_exists wa _ "n" _ (ZeroFrame.u64_storable n (by omega))
  have wn:=wellScoped_declare wa dn
  obtain ⟨sm,dm⟩:=ZeroFrame.declare_exists wn _ "m" _ (ZeroFrame.u64_storable factor ff)
  have wm:=wellScoped_declare wn dm
  obtain ⟨sj,dj⟩:=ZeroFrame.declare_exists wm _ "j" _ (ZeroFrame.u64_storable 0 (by norm_num))
  have wj:=wellScoped_declare wm dj
  obtain ⟨sc,dc⟩:=ZeroFrame.declare_exists wj _ "carry" _ (ZeroFrame.u64_storable 0 (by norm_num))
  have ia:=declare_storable (CopyLoop.pointer_storable object start)
    (CopyLoop.pointer_storable object start).converted da
  have inn:=declare_storable (ZeroFrame.u64_storable n (by omega)) (convert64 n (by omega)) dn
  have im:=declare_storable (ZeroFrame.u64_storable factor ff) (convert64 factor ff) dm
  have ij:=declare_storable (ZeroFrame.u64_storable 0 (by norm_num)) (convert64 0 (by norm_num)) dj
  have ic:=declare_storable (ZeroFrame.u64_storable 0 (by norm_num)) (convert64 0 (by norm_num)) dc
  have oa:=ia.nextObject
  have on:=inn.nextObject
  have om:=im.nextObject
  have oj:=ij.nextObject
  have saScope:=ia.scope
  have snScope:=inn.scope
  have smScope:=im.scope
  have sjScope:=ij.scope
  have oldObject : object<entry.nextObject:=well.objectIds _ _ rep.2.1
  have locals : Locals sc name type (ids entry.nextObject) entry.scope (values object start n factor 0 0):=by
    refine ⟨?_,?_,?_,?_⟩
    · intro v;cases v <;> simp [ids,name,type,ic.environment,ij.environment,im.environment,inn.environment,ia.environment,
        empty,oa,on,om,oj,scalarPointer,List.lookup]
    · intro v;cases v
      · have h1:=ApplicationBirthFrame.slot_declare_old wa ia.slot inn
        have h2:=ApplicationBirthFrame.slot_declare_old wn h1 im
        have h3:=ApplicationBirthFrame.slot_declare_old wm h2 ij
        have h4:=ApplicationBirthFrame.slot_declare_old wj h3 ic
        simpa only [ids,type,values] using h4
      · have h1:=ApplicationBirthFrame.slot_declare_old wn inn.slot im
        have h2:=ApplicationBirthFrame.slot_declare_old wm h1 ij
        have h3:=ApplicationBirthFrame.slot_declare_old wj h2 ic
        simpa only [ids,type,values,oa,saScope] using h3
      · have h1:=ApplicationBirthFrame.slot_declare_old wm im.slot ij
        have h2:=ApplicationBirthFrame.slot_declare_old wj h1 ic
        simpa only [ids,type,values,oa,on,saScope,snScope] using h2
      · have h1:=ApplicationBirthFrame.slot_declare_old wj ij.slot ic
        simpa only [ids,type,values,oa,on,om,saScope,snScope,smScope] using h1
      · simpa only [ids,type,values,oa,on,om,oj,saScope,snScope,smScope,sjScope] using ic.slot
    · intro v w same;cases v <;> cases w <;> simp_all [ids] <;> omega
    · rw [ic.nextScope,ij.nextScope,im.nextScope,inn.nextScope,ia.nextScope];exact well.current
  have host : sc.mode=.host:=ic.mode.trans (ij.mode.trans (im.mode.trans (inn.mode.trans (ia.mode.trans rep.1))))
  have array : WordArrayRep sc object length old:=by
    refine ⟨host,?_,rep.2.2⟩
    rw [ic.outside object (by omega),ij.outside object (by omega),im.outside object (by omega),
      inn.outside object (by omega),ia.outside object (by omega)]
    exact rep.2.1
  refine ⟨sa,sn,sm,sj,sc,da,dn,dm,dj,dc,?_,?_,?_,bound,small,by omega,digits,factorSmall,wellScoped_declare wj dc⟩
  · simpa only [currentData_zero] using array
  · simpa only [scaledRow,row] using locals
  · intro v;cases v <;> simp only [ids] <;> omega

theorem slot_store_exists {F : Type} {state : State F} {id owner : Nat}
    {ctype : CType} {oldValue : Value} (h : Slot state id owner ctype oldValue)
    (v : Value) (hv : Storable ctype v) : ∃after,state.store (scalarPointer id ctype) v=some after:=by
  obtain ⟨oldType,present⟩:=h
  have same : oldValue.byteSize=v.byteSize:=Option.some.inj (oldType.typeWidth.symm.trans hv.typeWidth)
  rw [same] at present
  simp [State.store,scalarPointer,present,scalarObject,State.accessible,hv.typeWidth,hv.converted]

#print axioms actual_body
#print axioms initialize_parameters
end RH080Next.FFTPV.MultiplySmallSource
