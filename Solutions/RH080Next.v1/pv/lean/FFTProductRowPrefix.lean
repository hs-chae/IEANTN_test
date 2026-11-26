/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTSourceProductRow
import FFTWordSlices
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.ProductRow
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots

theorem source_index_eval {F : Type} (context : Context F) (before : State F)
    (carray cindex : String) (arrayCell indexCell : Pointer)
    {object size start index : Nat} {data : Nat→Nat}
    (rep : WordArrayRep before object size data) (hi : start+index<size)
    (arrayNamed : before.environment.lookup carray=some arrayCell)
    (arrayRead : before.load arrayCell=some (.pointer (wordPointer object start)))
    (indexNamed : before.environment.lookup cindex=some indexCell)
    (indexRead : before.load indexCell=some (.integer (integer64 index))) :
    Eval context before (arrayAt carray cindex) (.integer (integer64 (data (start+index)))) before :=
  .load (.index (.variable arrayNamed arrayRead) (.variable indexNamed indexRead)
    (slice_pointer_add rep hi)) (word_load rep hi)

private theorem slot_survives_declaration {F : Type} {before after : State F}
    {id owner : Nat} {ctype dtype : CType} {old fresh : Value} {cname : String}
    (well : WellScoped before) (slot : Slot before id owner ctype old)
    (d : Declaration before after cname dtype fresh) : Slot after id owner ctype old := by
  have oldId:=well.objectIds id _ slot.object
  exact ⟨slot.storable,by rw [d.outside id (by omega)]; exact slot.object⟩

theorem actual_t_digit_prefix : (actualInner.drop 1).take 2 =
    [.declare .u64 "t" (some tExpr),digitStmt] := by
  rw [actual_inner_shape]
  rfl

/-- Proved frame of the actual t birth and scratch-word store. -/
structure PrefixFrame {F : Type} (before after : State F) (object t : Nat) : Prop where
  environment : after.environment=("t",scalarPointer before.nextObject .u64)::before.environment
  scope : after.scope=before.scope
  nextScope : after.nextScope=before.nextScope
  nextObject : after.nextObject=before.nextObject+1
  foreign : after.foreign=before.foreign
  well : WellScoped after
  tSlot : Slot after before.nextObject before.scope .u64 (.integer (integer64 t))
  oldObjects : ∀id,id<before.nextObject → id≠object → after.objects id=before.objects id

/-- Two actual inner-row source statements, including fresh t allocation,
array addressing at a genuine subrange offset, and the following carry read.
The input read premises are source observations, never an output certificate. -/
theorem t_digit_prefix_execution {F : Type} (context : Context F) (before : State F)
    (well : WellScoped before) (workId workOwner kId kOwner : Nat)
    (object size start k a b c : Nat) (data : Nat→Nat)
    (rep : WordArrayRep before object size data) (hk : start+k<size)
    (workName : before.environment.lookup "work"=some (scalarPointer workId (.pointer .u64)))
    (workSlot : Slot before workId workOwner (.pointer .u64) (.pointer (wordPointer object start)))
    (kName : before.environment.lookup "k"=some (scalarPointer kId .u64))
    (kSlot : Slot before kId kOwner .u64 (.integer (integer64 k)))
    (ha : a<1000000000) (hb : b<1000000000)
    (hd : data (start+k)<1000000000) (hc : c<1000000000)
    (readA : Eval context before (arrayAt "a" "i") (.integer (integer64 a)) before)
    (readB : Eval context before (arrayAt "b" "j") (.integer (integer64 b)) before)
    (readC : Eval context before (.variable "carry") (.integer (integer64 c)) before) :
    ∃after,ExecList context before [.declare .u64 "t" (some tExpr),digitStmt] .normal after ∧
      WordArrayRep after object size (Function.update data (start+k)
        ((data (start+k)+a*b+c)%1000000000)) ∧
      Eval context after carryExpr (.integer (integer64 ((data (start+k)+a*b+c)/1000000000))) after ∧
      RH080Next.FFT.Limbs.value 1000000000 size
          (Function.update data (start+k) ((data (start+k)+a*b+c)%1000000000))+
        (((data (start+k)+a*b+c)/1000000000:Nat):Int)*(1000000000:Int)^(start+k+1)=
      RH080Next.FFT.Limbs.value 1000000000 size data+
        ((a*b+c:Nat):Int)*(1000000000:Int)^(start+k) ∧
      PrefixFrame before after object (data (start+k)+a*b+c) := by
  let t:=data (start+k)+a*b+c
  have ht : t<2^64 := schoolbook_digit_safe a b _ c ha hb hd hc
  have readD:=source_index_eval context before "work" "k" _ _ rep hk workName workSlot.read kName kSlot.read
  have evalT:=source_t_eval context before a b _ c ha hb hd hc readA readB readD readC
  obtain ⟨middle,declRun,dt⟩ := source_t_declaration context before well t ht evalT
  have objectOld:=well.objectIds object _ rep.2.1
  have rm : WordArrayRep middle object size data :=
    ⟨dt.mode.trans rep.1,by rw [dt.outside object (by omega)]; exact rep.2.1,rep.2.2⟩
  have wm:=slot_survives_declaration well workSlot dt
  have km:=slot_survives_declaration well kSlot dt
  have workNamed : middle.environment.lookup "work"=some (scalarPointer workId (.pointer .u64)) := by
    rw [dt.environment]
    simpa [List.lookup] using workName
  have kNamed : middle.environment.lookup "k"=some (scalarPointer kId .u64) := by
    rw [dt.environment]
    simpa [List.lookup] using kName
  have tNamed : middle.environment.lookup "t"=some (scalarPointer before.nextObject .u64) := by
    rw [dt.environment]
    rfl
  have placeWork : Place context middle (arrayAt "work" "k") (wordPointer object (start+k)) middle :=
    .index (.variable workNamed wm.read) (.variable kNamed km.read) (slice_pointer_add rm hk)
  have readT : Eval context middle (.variable "t") (.integer (integer64 t)) middle :=
    .variable tNamed dt.slot.read
  have hv : t%1000000000<2^64 := lt_trans (Nat.mod_lt _ (by norm_num)) (by norm_num)
  obtain ⟨after,stored,ra⟩ := word_store_with_rep rm hk hv
  have storeRun : Exec context middle digitStmt .normal after := by
    apply Exec.assign (value:=.integer (integer64 (t%1000000000)))
      (Eval.paren (Eval.binaryLR readT
        (.literal (.integer 1000000000 "ULL") _ (.integer (integer64 1000000000)) (by rfl))
        (by simp only [binary,binary64_mod t 1000000000 ht (by norm_num) (by norm_num),Option.map_some]))) placeWork
    exact stored
  obtain ⟨env,mode,scope,ns,no,outside⟩:=store_frame stored
  have ta : Slot after before.nextObject before.scope .u64 (.integer (integer64 t)) :=
    ⟨dt.slot.storable,by rw [outside _ (by change before.nextObject≠object; omega)]; exact dt.slot.object⟩
  have readTA : Eval context after (.variable "t") (.integer (integer64 t)) after :=
    .variable (by rw [env]; exact tNamed) ta.read
  have middleMeta : WellScoped middle ∧ middle.foreign=before.foreign := by
    cases declRun with
    | declareSome evaluated declared =>
      have same:=SourcePure.eval_state evaluated
        (by simp [tExpr,arrayAt,SourcePure.CallFree])
      subst_vars
      exact ⟨wellScoped_declare well declared,declare_foreign declared⟩
  have pf : PrefixFrame before after object t := by
    refine ⟨env.trans dt.environment,scope.trans dt.scope,ns.trans dt.nextScope,
      no.trans dt.nextObject,(store_foreign stored).trans middleMeta.2,
      wellScoped_store middleMeta.1 stored,ta,?_⟩
    intro id old different
    rw [outside id different,dt.outside id (by omega)]
  exact ⟨after,.cons declRun (.cons storeRun .nil),ra,source_carry_eval context after t ht readTA,
    source_row_conservation size (start+k) a b c data hk,pf⟩

#print axioms source_index_eval
#print axioms actual_t_digit_prefix
#print axioms t_digit_prefix_execution
end RH080Next.FFTPV.ProductRow
