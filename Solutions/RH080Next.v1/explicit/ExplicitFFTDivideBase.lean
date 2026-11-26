/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTDivideData
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.DivideSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings
open FFT.Limbs
open IncrementSource (base)

inductive Var where | a | n | d | ceiling | j | rem deriving DecidableEq
def name : Var → String | .a=>"a" | .n=>"n" | .d=>"d" | .ceiling=>"ceiling" | .j=>"j" | .rem=>"rem"
def type : Var → CType | .a=>.pointer .u64 | _=>.u64
def values (object start n d ceiling j rem : Nat) : Var → Value
  | .a=>.pointer (wordPointer object start)
  | .n=>.integer (integer64 n)
  | .d=>.integer (integer64 d)
  | .ceiling=>.integer (integer64 ceiling)
  | .j=>.integer (integer64 j)
  | .rem=>.integer (integer64 rem)
def ids (first : Nat) : Var → Nat
  | .a=>first | .n=>first+1 | .d=>first+2 | .ceiling=>first+3 | .j=>first+4 | .rem=>first+5

def condition : Expr:=.binary .gt (.variable "j") (.literal (.integer 0 "ULL"))
def decrement : Stmt:=.assign (.variable "j") (.paren (.binary .sub (.variable "j") (.literal (.integer 1 "ULL"))))
def tExpr : Expr:=.paren (.binary .add (.paren (.binary .mul (.variable "rem") (.literal (.integer 1000000000 "ULL"))))
  (.index (.variable "a") (.variable "j")))
def digitStmt : Stmt:=.assign (.index (.variable "a") (.variable "j")) (.paren (.binary .div (.variable "t") (.variable "d")))
def remainderStmt : Stmt:=.assign (.variable "rem") (.paren (.binary .mod (.variable "t") (.variable "d")))
def loopBody : Stmt:=.block [decrement,.declare .u64 "t" (some tExpr),digitStmt,remainderStmt]
def loop : Stmt:=.whileLoop condition loopBody

structure View {F : Type} (state : State F) (object length start n d ceiling owner : Nat)
    (li : Var → Nat) (old : Nat → Nat) (j : Nat) : Prop where
  array : WordArrayRep state object length (currentData old start n d j)
  locals : Locals state name type li owner (values object start n d ceiling j (division old start n d j).2)
  separate : ∀v,object≠li v
  bound : start+n ≤ length
  small : n ≤ 6
  active : j ≤ n
  digits : ∀i < n,old (start+i) < base
  divisor_positive : 0 < d
  divisor_bound : d < base
  ceiling_bound : ceiling ≤ 1
  well : WellScoped state

theorem View.enter {F : Type} {state : State F} {object length start n d ceiling owner j : Nat}
    {li : Var → Nat} {old : Nat → Nat} (h : View state object length start n d ceiling owner li old j) :
    View state.enterScope object length start n d ceiling owner li old j :=
  ⟨h.array,h.locals.enter,h.separate,h.bound,h.small,h.active,h.digits,h.divisor_positive,
    h.divisor_bound,h.ceiling_bound,wellScoped_enter h.well⟩

theorem initialize_parameters {F : Type} {entry : State F} {object length start n d ceiling : Nat}
    {old : Nat → Nat} (well : WellScoped entry) (empty : entry.environment=[])
    (rep : WordArrayRep entry object length old) (bound : start+n ≤ length) (small : n ≤ 6)
    (digits : ∀i < n,old (start+i) < base) (hd : 0 < d) (hdb : d < base) (hceil : ceiling ≤ 1) :
    ∃sa sn sd sce sj sr,
      entry.declare (.pointer .u64) "a" (some (.pointer (wordPointer object start)))=some sa ∧
      sa.declare .u64 "n" (some (.integer (integer64 n)))=some sn ∧
      sn.declare .u64 "d" (some (.integer (integer64 d)))=some sd ∧
      sd.declare .u64 "ceiling" (some (.integer (integer64 ceiling)))=some sce ∧
      sce.declare .u64 "j" (some (.integer (integer64 n)))=some sj ∧
      sj.declare .u64 "rem" (some (.integer (integer64 0)))=some sr ∧
      View sr object length start n d ceiling entry.scope (ids entry.nextObject) old n := by
  obtain ⟨sa,da⟩:=ZeroFrame.declare_exists well _ "a" _ (CompareSource.pointer_storable object start)
  have wa:=wellScoped_declare well da
  obtain ⟨sn,dn⟩:=ZeroFrame.declare_exists wa _ "n" _ (ZeroFrame.u64_storable n (by omega))
  have wn:=wellScoped_declare wa dn
  obtain ⟨sd,dd⟩:=ZeroFrame.declare_exists wn _ "d" _ (ZeroFrame.u64_storable d (by dsimp [base] at hdb; omega))
  have wd:=wellScoped_declare wn dd
  obtain ⟨sce,dce⟩:=ZeroFrame.declare_exists wd _ "ceiling" _ (ZeroFrame.u64_storable ceiling (by omega))
  have wce:=wellScoped_declare wd dce
  obtain ⟨sj,dj⟩:=ZeroFrame.declare_exists wce _ "j" _ (ZeroFrame.u64_storable n (by omega))
  have wj:=wellScoped_declare wce dj
  obtain ⟨sr,dr⟩:=ZeroFrame.declare_exists wj _ "rem" _ (ZeroFrame.u64_storable 0 (by norm_num))
  have ia:=declare_storable (CompareSource.pointer_storable object start) (CompareSource.pointer_storable object start).converted da
  have inn:=declare_storable (ZeroFrame.u64_storable n (by omega)) (convert64 n (by omega)) dn
  have idd:=declare_storable (ZeroFrame.u64_storable d (by dsimp [base] at hdb; omega)) (convert64 d (by dsimp [base] at hdb; omega)) dd
  have ice:=declare_storable (ZeroFrame.u64_storable ceiling (by omega)) (convert64 ceiling (by omega)) dce
  have ij:=declare_storable (ZeroFrame.u64_storable n (by omega)) (convert64 n (by omega)) dj
  have ir:=declare_storable (ZeroFrame.u64_storable 0 (by norm_num)) (convert64 0 (by norm_num)) dr
  have no0:=ia.nextObject
  have sc0:=ia.scope
  have no1:=inn.nextObject
  have sc1:=inn.scope
  have no2:=idd.nextObject
  have sc2:=idd.scope
  have no3:=ice.nextObject
  have sc3:=ice.scope
  have no4:=ij.nextObject
  have sc4:=ij.scope
  have no5:=ir.nextObject
  have sc5:=ir.scope
  have lm : Locals sr name type (ids entry.nextObject) entry.scope (values object start n d ceiling n 0) := by
    constructor
    · intro v
      cases v <;> simp [ids,name,type,ir.environment,ij.environment,ice.environment,idd.environment,inn.environment,ia.environment,empty,scalarPointer,List.lookup,no0,no1,no2,no3,no4,no5]
    · intro v
      cases v with
      | a=>
        have h1:=ApplicationBirthFrame.slot_declare_old wa ia.slot inn
        have h2:=ApplicationBirthFrame.slot_declare_old wn h1 idd
        have h3:=ApplicationBirthFrame.slot_declare_old wd h2 ice
        have h4:=ApplicationBirthFrame.slot_declare_old wce h3 ij
        have h5:=ApplicationBirthFrame.slot_declare_old wj h4 ir
        simpa only [ids,type,values] using h5
      | n=>
        have h2:=ApplicationBirthFrame.slot_declare_old wn inn.slot idd
        have h3:=ApplicationBirthFrame.slot_declare_old wd h2 ice
        have h4:=ApplicationBirthFrame.slot_declare_old wce h3 ij
        have h5:=ApplicationBirthFrame.slot_declare_old wj h4 ir
        simpa only [ids,type,values,no0,sc0] using h5
      | d=>
        have h3:=ApplicationBirthFrame.slot_declare_old wd idd.slot ice
        have h4:=ApplicationBirthFrame.slot_declare_old wce h3 ij
        have h5:=ApplicationBirthFrame.slot_declare_old wj h4 ir
        simpa only [ids,type,values,no0,no1,sc0,sc1] using h5
      | ceiling=>
        have h4:=ApplicationBirthFrame.slot_declare_old wce ice.slot ij
        have h5:=ApplicationBirthFrame.slot_declare_old wj h4 ir
        simpa only [ids,type,values,no0,no1,no2,sc0,sc1,sc2] using h5
      | j=>
        have h5:=ApplicationBirthFrame.slot_declare_old wj ij.slot ir
        simpa only [ids,type,values,no0,no1,no2,no3,sc0,sc1,sc2,sc3] using h5
      | rem=>
        simpa only [ids,type,values,no0,no1,no2,no3,no4,sc0,sc1,sc2,sc3,sc4] using ir.slot
    · intro v w eq
      cases v <;> cases w <;> simp_all [ids] <;> omega
    · rw [ir.nextScope,ij.nextScope,ice.nextScope,idd.nextScope,inn.nextScope,ia.nextScope]
      exact well.current
  have chain : Declarations entry sr:=.cons da (.cons dn (.cons dd (.cons dce (.cons dj (.cons dr (.nil sr))))))
  have fields:=chain.fields
  have oldObject:=well.objectIds object _ rep.2.1
  have array : WordArrayRep sr object length old:=
    ⟨fields.2.2.2.1.trans rep.1,by rw [fields.2.2.2.2 object oldObject]; exact rep.2.1,rep.2.2⟩
  refine ⟨sa,sn,sd,sce,sj,sr,da,dn,dd,dce,dj,dr,?_,?_,?_,bound,small,le_refl _,digits,hd,hdb,hceil,wellScoped_declare wj dr⟩
  · simpa only [currentData_initial] using array
  · simpa only [division_initial] using lm
  · intro v
    cases v <;> simp only [ids] <;> omega

#print axioms initialize_parameters
end RH080Next.FFTPV.DivideSource
