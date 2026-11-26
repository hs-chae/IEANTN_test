/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTAddMagnitudeModel
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.AddMagnitudeSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings

inductive Var where | out | a | n | i | carry deriving DecidableEq

def name : Var → String | .out=>"out" | .a=>"a" | .n=>"n" | .i=>"i" | .carry=>"carry"
def ctype : Var → CType | .out | .a=>.pointer .u64 | _=>.u64
def values (input : Input) (j : Nat) : Var → Value
  | .out=>.pointer (wordPointer input.layout.outObject input.layout.outStart)
  | .a=>.pointer (wordPointer input.layout.aObject input.layout.aStart)
  | .n=>.integer (integer64 input.layout.n)
  | .i=>.integer (integer64 j)
  | .carry=>.integer (integer64 (row input j).2)
def ids (first : Nat) : Var → Nat | .out=>first | .a=>first+1 | .n=>first+2 | .i=>first+3 | .carry=>first+4

structure View {F : Type} (state : State F) (input : Input) (owner : Nat) (li : Var → Nat) (j : Nat) : Prop where
  array : WordArrayRep state input.layout.outObject (input.layout.length input.layout.outObject) (currentData input j)
  inputArray : ∃data,WordArrayRep state input.layout.aObject (input.layout.length input.layout.aObject) data ∧
    ∀k<5,data (input.layout.aStart+k)=input.old input.layout.aObject (input.layout.aStart+k)
  locals : Locals state name ctype li owner (values input j)
  separate : ∀v,input.layout.outObject≠li v ∧ input.layout.aObject≠li v
  active : j≤ input.layout.n
  well : WellScoped state

theorem View.enter {F : Type} {state : State F} {input : Input} {owner : Nat} {li : Var → Nat} {j : Nat}
    (h : View state input owner li j) : View state.enterScope input owner li j:=
  ⟨h.array,h.inputArray,h.locals.enter,h.separate,h.active,wellScoped_enter h.well⟩

def condition : Expr:=.binary .lt (.variable "i") (.variable "n")
def indexA : Expr:=.index (.variable "a") (.variable "i")
def xAssign : Stmt:=.assign (.variable "x") indexA

def xBranch : Stmt:=.ite (.binary .lt (.variable "i") (.literal (.integer 5 "ULL"))) (.block [xAssign]) none

def tExpr : Expr:=.paren (.binary .add (.paren (.binary .add (.index (.variable "out") (.variable "i")) (.variable "x"))) (.variable "carry"))
def digitStmt : Stmt:=.assign (.index (.variable "out") (.variable "i"))
  (.paren (.binary .mod (.variable "t") (.literal (.integer base "ULL"))))
def carryStmt : Stmt:=.assign (.variable "carry")
  (.paren (.binary .div (.variable "t") (.literal (.integer base "ULL"))))
def advanceStmt : Stmt:=.assign (.variable "i") (.paren (.binary .add (.variable "i") (.literal (.integer 1 "ULL"))))
def bodyStatements : List Stmt:=[.declare .u64 "x" (some (.literal (.integer 0 "ULL"))),xBranch,
  .declare .u64 "t" (some tExpr),digitStmt,carryStmt,advanceStmt]
def loopBody : Stmt:=.block bodyStatements
def loop : Stmt:=.whileLoop condition loopBody

theorem actual_body : add_magnitude_ast.body=.block [
    .declare .u64 "i" (some (.literal (.integer 0 "ULL"))),
    .declare .u64 "carry" (some (.literal (.integer 0 "ULL"))),loop,.returnValue (some (.variable "carry"))]:=rfl

/-- Both actual pointer parameters, n and the two persistent source locals
are allocated at their true lifetime owner. Input array contents are established
by the caller's actual typed arrays, not an initialized-application premise. -/
theorem initialize_parameters {F : Type} {entry : State F} (input : Input)
    (well : WellScoped entry) (empty : entry.environment=[])
    (outRep : WordArrayRep entry input.layout.outObject (input.layout.length input.layout.outObject) (input.old input.layout.outObject))
    (aRep : WordArrayRep entry input.layout.aObject (input.layout.length input.layout.aObject) (input.old input.layout.aObject)) :
    ∃so sa sn si sc,
      entry.declare (.pointer .u64) "out" (some (.pointer (wordPointer input.layout.outObject input.layout.outStart)))=some so ∧
      so.declare (.pointer .u64) "a" (some (.pointer (wordPointer input.layout.aObject input.layout.aStart)))=some sa ∧
      sa.declare .u64 "n" (some (.integer (integer64 input.layout.n)))=some sn ∧
      sn.declare .u64 "i" (some (.integer (integer64 0)))=some si ∧
      si.declare .u64 "carry" (some (.integer (integer64 0)))=some sc ∧
      View sc input entry.scope (ids entry.nextObject) 0:=by
  have n64 : input.layout.n<2^64:=by have hn:=input.layout.small;omega
  obtain ⟨so,dOut⟩:=ZeroFrame.declare_exists well _ "out" _ (CompareSource.pointer_storable input.layout.outObject input.layout.outStart)
  have wo:=wellScoped_declare well dOut
  obtain ⟨sa,da⟩:=ZeroFrame.declare_exists wo _ "a" _ (CompareSource.pointer_storable input.layout.aObject input.layout.aStart)
  have wa:=wellScoped_declare wo da
  obtain ⟨sn,dn⟩:=ZeroFrame.declare_exists wa _ "n" _ (ZeroFrame.u64_storable input.layout.n n64)
  have wn:=wellScoped_declare wa dn
  obtain ⟨si,di⟩:=ZeroFrame.declare_exists wn _ "i" _ (ZeroFrame.u64_storable 0 (by norm_num))
  have wi:=wellScoped_declare wn di
  obtain ⟨sc,dc⟩:=ZeroFrame.declare_exists wi _ "carry" _ (ZeroFrame.u64_storable 0 (by norm_num))
  have io:=declare_storable (CompareSource.pointer_storable input.layout.outObject input.layout.outStart)
    (CompareSource.pointer_storable input.layout.outObject input.layout.outStart).converted dOut
  have ia:=declare_storable (CompareSource.pointer_storable input.layout.aObject input.layout.aStart)
    (CompareSource.pointer_storable input.layout.aObject input.layout.aStart).converted da
  have inn:=declare_storable (ZeroFrame.u64_storable input.layout.n n64) (convert64 _ n64) dn
  have ii:=declare_storable (ZeroFrame.u64_storable 0 (by norm_num)) (convert64 0 (by norm_num)) di
  have ic:=declare_storable (ZeroFrame.u64_storable 0 (by norm_num)) (convert64 0 (by norm_num)) dc
  have oo:=io.nextObject
  have oa:=ia.nextObject
  have on:=inn.nextObject
  have oi:=ii.nextObject
  have soScope:=io.scope
  have saScope:=ia.scope
  have snScope:=inn.scope
  have siScope:=ii.scope
  have declarations : Declarations entry sc:=.cons dOut (.cons da (.cons dn (.cons di (.cons dc (.nil sc)))))
  have oldOut:=well.objectIds _ _ outRep.2.1
  have oldA:=well.objectIds _ _ aRep.2.1
  have lm : Locals sc name ctype (ids entry.nextObject) entry.scope (values input 0):=by
    constructor
    · intro v;cases v <;> simp [name,ctype,ids,ic.environment,ii.environment,inn.environment,ia.environment,io.environment,empty,oo,oa,on,oi,List.lookup]
    · intro v;cases v
      · have h1:=ApplicationBirthFrame.slot_declare_old wo io.slot ia
        have h2:=ApplicationBirthFrame.slot_declare_old wa h1 inn
        have h3:=ApplicationBirthFrame.slot_declare_old wn h2 ii
        have h4:=ApplicationBirthFrame.slot_declare_old wi h3 ic
        simpa only [ctype,ids,values] using h4
      · have h1:=ApplicationBirthFrame.slot_declare_old wa ia.slot inn
        have h2:=ApplicationBirthFrame.slot_declare_old wn h1 ii
        have h3:=ApplicationBirthFrame.slot_declare_old wi h2 ic
        simpa only [ctype,ids,values,oo,soScope] using h3
      · have h1:=ApplicationBirthFrame.slot_declare_old wn inn.slot ii
        have h2:=ApplicationBirthFrame.slot_declare_old wi h1 ic
        simpa only [ctype,ids,values,oo,oa,soScope,saScope] using h2
      · have h1:=ApplicationBirthFrame.slot_declare_old wi ii.slot ic
        simpa only [ctype,ids,values,oo,oa,on,soScope,saScope,snScope] using h1
      · simpa only [ctype,ids,values,oo,oa,on,oi,soScope,saScope,snScope,siScope,row,FFT.Limbs.addDigits] using ic.slot
    · intro a b same;cases a <;> cases b <;> simp_all [ids] <;> omega
    · rw [ic.nextScope,ii.nextScope,inn.nextScope,ia.nextScope,io.nextScope];exact well.current
  have out : WordArrayRep sc input.layout.outObject (input.layout.length input.layout.outObject) (currentData input 0):=by
    refine ⟨declarations.fields.2.2.2.1.trans outRep.1,?_,outRep.2.2⟩
    rw [declarations.fields.2.2.2.2 _ oldOut];exact outRep.2.1
  have a : WordArrayRep sc input.layout.aObject (input.layout.length input.layout.aObject) (input.old input.layout.aObject):=by
    refine ⟨declarations.fields.2.2.2.1.trans aRep.1,?_,aRep.2.2⟩
    rw [declarations.fields.2.2.2.2 _ oldA];exact aRep.2.1
  exact ⟨so,sa,sn,si,sc,dOut,da,dn,di,dc,out,⟨_,a,fun _ _=>rfl⟩,lm,
    (by intro v;cases v <;> simp only [ids] <;> constructor <;> omega),by omega,wellScoped_declare wi dc⟩

#print axioms initialize_parameters
end RH080Next.FFTPV.AddMagnitudeSource
