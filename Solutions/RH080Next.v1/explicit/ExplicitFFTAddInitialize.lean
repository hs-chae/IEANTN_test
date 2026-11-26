/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTAddAST
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.AddSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings
open FFT.Limbs
open IncrementSource (base)

inductive PreVar where | out | a | b | subtract | asign | bsign deriving DecidableEq
def preName : PreVar → String | .out=>"out" | .a=>"a" | .b=>"b" | .subtract=>"subtract" | .asign=>"as" | .bsign=>"bs"
def preType : PreVar → CType | .out | .a | .b=>.pointer .u64 | _=>.u64
def preValues (i : Input) (bs : Nat) : PreVar → Value
  | .out=>.pointer (wordPointer (i.layout.object .out) (i.layout.start .out))
  | .a=>.pointer (wordPointer (i.layout.object .a) (i.layout.start .a))
  | .b=>.pointer (wordPointer (i.layout.object .b) (i.layout.start .b))
  | .subtract=>.integer (integer64 i.subtract)
  | .asign=>.integer (integer64 i.asign)
  | .bsign=>.integer (integer64 bs)
def preIds (first : Nat) : PreVar → Nat
  | .out=>first | .a=>first+1 | .b=>first+2 | .subtract=>first+3 | .asign=>first+4 | .bsign=>first+5

structure PreView {F : Type} (state : State F) (input : Input) (owner : Nat) (pi : PreVar → Nat) (bs : Nat) : Prop where
  arrays : ∀r,WordArrayRep state (input.layout.object r) (input.layout.length (input.layout.object r)) (input.old (input.layout.object r))
  locals : Locals state preName preType pi owner (preValues input bs)
  separate : ∀r v,input.layout.object r≠pi v
  well : WellScoped state

theorem PreView.enter {F : Type} {state : State F} {input : Input} {owner bs : Nat} {pi : PreVar → Nat}
    (h : PreView state input owner pi bs) : PreView state.enterScope input owner pi bs :=
  ⟨h.arrays,h.locals.enter,h.separate,wellScoped_enter h.well⟩

/-- Actual four pointer/flag parameter births, followed by the source's two
sign reads and declarations. No pre-existing application binding is assumed. -/
theorem initialize_signs {F : Type} (context : Context F) {entry : State F} (input : Input)
    (well : WellScoped entry) (empty : entry.environment=[])
    (rep : ∀r,WordArrayRep entry (input.layout.object r) (input.layout.length (input.layout.object r)) (input.old (input.layout.object r))) :
    ∃so sa sb sp sas sbs,
      entry.declare (.pointer .u64) "out" (some (.pointer (wordPointer (input.layout.object .out) (input.layout.start .out))))=some so ∧
      so.declare (.pointer .u64) "a" (some (.pointer (wordPointer (input.layout.object .a) (input.layout.start .a))))=some sa ∧
      sa.declare (.pointer .u64) "b" (some (.pointer (wordPointer (input.layout.object .b) (input.layout.start .b))))=some sb ∧
      sb.declare .u64 "subtract" (some (.integer (integer64 input.subtract)))=some sp ∧
      sp.declare .u64 "as" (some (.integer (integer64 input.asign)))=some sas ∧
      sas.declare .u64 "bs" (some (.integer (integer64 (input.old (input.layout.object .b) (input.layout.start .b+5)))))=some sbs ∧
      ExecList context sp [asDeclaration,bsDeclaration] .normal sbs ∧
      PreView sbs input entry.scope (preIds entry.nextObject) (input.old (input.layout.object .b) (input.layout.start .b+5)) := by
  have sub64 : input.subtract < 2^64:=by have hs:=input.subtract_bound; omega
  have as64 : input.asign < 2^64:=by have hs:=input.signA; exact lt_of_le_of_lt hs (by norm_num)
  have bs64 : input.old (input.layout.object .b) (input.layout.start .b+5) < 2^64:=lt_of_le_of_lt input.signB (by norm_num)
  obtain ⟨so,dout⟩:=ZeroFrame.declare_exists well _ "out" _ (CompareSource.pointer_storable (input.layout.object .out) (input.layout.start .out))
  have wo:=wellScoped_declare well dout
  obtain ⟨sa,da⟩:=ZeroFrame.declare_exists wo _ "a" _ (CompareSource.pointer_storable (input.layout.object .a) (input.layout.start .a))
  have wa:=wellScoped_declare wo da
  obtain ⟨sb,db⟩:=ZeroFrame.declare_exists wa _ "b" _ (CompareSource.pointer_storable (input.layout.object .b) (input.layout.start .b))
  have wb:=wellScoped_declare wa db
  obtain ⟨sp,dp⟩:=ZeroFrame.declare_exists wb _ "subtract" _ (ZeroFrame.u64_storable input.subtract sub64)
  have wp:=wellScoped_declare wb dp
  have io:=declare_storable (CompareSource.pointer_storable (input.layout.object .out) (input.layout.start .out)) (CompareSource.pointer_storable (input.layout.object .out) (input.layout.start .out)).converted dout
  have ia:=declare_storable (CompareSource.pointer_storable (input.layout.object .a) (input.layout.start .a)) (CompareSource.pointer_storable (input.layout.object .a) (input.layout.start .a)).converted da
  have ib:=declare_storable (CompareSource.pointer_storable (input.layout.object .b) (input.layout.start .b)) (CompareSource.pointer_storable (input.layout.object .b) (input.layout.start .b)).converted db
  have ip:=declare_storable (ZeroFrame.u64_storable input.subtract sub64) (convert64 input.subtract sub64) dp
  have params : Declarations entry sp:=.cons dout (.cons da (.cons db (.cons dp (.nil sp))))
  have rp : ∀r,WordArrayRep sp (input.layout.object r) (input.layout.length (input.layout.object r)) (input.old (input.layout.object r)):=by
    intro r
    have oldId:=well.objectIds _ _ (rep r).2.1
    exact ⟨params.fields.2.2.2.1.trans (rep r).1,by rw [params.fields.2.2.2.2 _ oldId]; exact (rep r).2.1,(rep r).2.2⟩
  have aSlot:=ApplicationBirthFrame.slot_declare_old wb (ApplicationBirthFrame.slot_declare_old wa ia.slot ib) ip
  have bSlot:=ApplicationBirthFrame.slot_declare_old wb ib.slot ip
  have aName : sp.environment.lookup "a"=some (scalarPointer so.nextObject (.pointer .u64)):=by simp [ip.environment,ib.environment,ia.environment,List.lookup]
  have bName : sp.environment.lookup "b"=some (scalarPointer sa.nextObject (.pointer .u64)):=by simp [ip.environment,ib.environment,List.lookup]
  have aIndex : input.layout.start .a+5 < input.layout.length (input.layout.object .a):=by have hb:=input.layout.bound .a; omega
  have bIndex : input.layout.start .b+5 < input.layout.length (input.layout.object .b):=by have hb:=input.layout.bound .b; omega
  have readA : Eval context sp (.index (.variable "a") (.literal (.integer 5 "ULL"))) (.integer (integer64 input.asign)) sp:=
    .load (.index (.variable aName aSlot.read) (.literal (.integer 5 "ULL") _ (.integer (integer64 5)) (by rfl))
      (slice_pointer_add (rp .a) aIndex)) (word_load (rp .a) aIndex)
  obtain ⟨sas,das⟩:=ZeroFrame.declare_exists wp _ "as" _ (ZeroFrame.u64_storable input.asign as64)
  have ias:=declare_storable (ZeroFrame.u64_storable input.asign as64) (convert64 input.asign as64) das
  have was:=wellScoped_declare wp das
  have bas:=ApplicationBirthFrame.slot_declare_old wp bSlot ias
  have ras:=ApplicationBirthFrame.array_declare_old wp (rp .b) ias
  have bNamed : sas.environment.lookup "b"=some (scalarPointer sa.nextObject (.pointer .u64)):=by rw [ias.environment]; simpa [List.lookup] using bName
  have readB : Eval context sas (.index (.variable "b") (.literal (.integer 5 "ULL")))
      (.integer (integer64 (input.old (input.layout.object .b) (input.layout.start .b+5)))) sas:=
    .load (.index (.variable bNamed bas.read) (.literal (.integer 5 "ULL") _ (.integer (integer64 5)) (by rfl))
      (slice_pointer_add ras bIndex)) (word_load ras bIndex)
  obtain ⟨sbs,dbs⟩:=ZeroFrame.declare_exists was _ "bs" _ (ZeroFrame.u64_storable _ bs64)
  have ibs:=declare_storable (ZeroFrame.u64_storable _ bs64) (convert64 _ bs64) dbs
  have no0:=io.nextObject
  have sc0:=io.scope
  have no1:=ia.nextObject
  have sc1:=ia.scope
  have no2:=ib.nextObject
  have sc2:=ib.scope
  have no3:=ip.nextObject
  have sc3:=ip.scope
  have no4:=ias.nextObject
  have sc4:=ias.scope
  have no5:=ibs.nextObject
  have sc5:=ibs.scope
  have lm : Locals sbs preName preType (preIds entry.nextObject) entry.scope (preValues input (input.old (input.layout.object .b) (input.layout.start .b+5))) := by
    constructor
    · intro v
      cases v <;> simp [preIds,preName,preType,ibs.environment,ias.environment,ip.environment,ib.environment,ia.environment,io.environment,empty,scalarPointer,List.lookup,no0,no1,no2,no3,no4]
    · intro v
      cases v with
      | out=>
        have h1:=ApplicationBirthFrame.slot_declare_old wo io.slot ia
        have h2:=ApplicationBirthFrame.slot_declare_old wa h1 ib
        have h3:=ApplicationBirthFrame.slot_declare_old wb h2 ip
        have h4:=ApplicationBirthFrame.slot_declare_old wp h3 ias
        have h5:=ApplicationBirthFrame.slot_declare_old was h4 ibs
        simpa only [preIds,preType,preValues] using h5
      | a=>
        have h2:=ApplicationBirthFrame.slot_declare_old wa ia.slot ib
        have h3:=ApplicationBirthFrame.slot_declare_old wb h2 ip
        have h4:=ApplicationBirthFrame.slot_declare_old wp h3 ias
        have h5:=ApplicationBirthFrame.slot_declare_old was h4 ibs
        simpa only [preIds,preType,preValues,no0,sc0] using h5
      | b=>
        have h3:=ApplicationBirthFrame.slot_declare_old wb ib.slot ip
        have h4:=ApplicationBirthFrame.slot_declare_old wp h3 ias
        have h5:=ApplicationBirthFrame.slot_declare_old was h4 ibs
        simpa only [preIds,preType,preValues,no0,no1,sc0,sc1] using h5
      | subtract=>
        have h4:=ApplicationBirthFrame.slot_declare_old wp ip.slot ias
        have h5:=ApplicationBirthFrame.slot_declare_old was h4 ibs
        simpa only [preIds,preType,preValues,no0,no1,no2,sc0,sc1,sc2] using h5
      | asign=>
        have h5:=ApplicationBirthFrame.slot_declare_old was ias.slot ibs
        simpa only [preIds,preType,preValues,no0,no1,no2,no3,sc0,sc1,sc2,sc3] using h5
      | bsign=>
        simpa only [preIds,preType,preValues,no0,no1,no2,no3,no4,sc0,sc1,sc2,sc3,sc4] using ibs.slot
    · intro v w eq
      cases v <;> cases w <;> simp_all [preIds] <;> omega
    · rw [ibs.nextScope,ias.nextScope,ip.nextScope,ib.nextScope,ia.nextScope,io.nextScope]
      exact well.current
  have chain : Declarations entry sbs:=.cons dout (.cons da (.cons db (.cons dp (.cons das (.cons dbs (.nil sbs))))))
  have arrays : ∀r,WordArrayRep sbs (input.layout.object r) (input.layout.length (input.layout.object r)) (input.old (input.layout.object r)):=by
    intro r
    have oldId:=well.objectIds _ _ (rep r).2.1
    exact ⟨chain.fields.2.2.2.1.trans (rep r).1,by rw [chain.fields.2.2.2.2 _ oldId]; exact (rep r).2.1,(rep r).2.2⟩
  have sep : ∀r v,input.layout.object r≠preIds entry.nextObject v := by
    intro r v
    have oldId:=well.objectIds _ _ (rep r).2.1
    cases v <;> simp only [preIds] <;> omega
  exact ⟨so,sa,sb,sp,sas,sbs,dout,da,db,dp,das,dbs,
    .cons (.declareSome readA das) (.cons (.declareSome readB dbs) .nil),⟨arrays,lm,sep,wellScoped_declare was dbs⟩⟩

#print axioms initialize_signs
end RH080Next.FFTPV.AddSource
