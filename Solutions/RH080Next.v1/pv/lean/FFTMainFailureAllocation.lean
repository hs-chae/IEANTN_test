import FFTMainMemoryContract
import ExplicitApplicationPureCall
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.MainAllocation
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings ApplicationBirthFrame

def nullablePointer : Option Nat → Value
  | none => .null
  | some object => .pointer (wordPointer object 0)

theorem nullablePointer_storable (object : Option Nat) :
    Storable (.pointer .u64) (nullablePointer object) := by
  cases object with
  | none => exact ⟨rfl,by decide,rfl⟩
  | some object => exact ZeroFrame.pointer_storable object

/-- Classifies every evaluation of the source calloc expression. The actual
allocator choice, including NULL, determines the actual resulting state. -/
theorem calloc_expression_cases {F : Type} (context : Context F) {before after : State F}
    {count : Expr} {size : Nat} {value : Value}
    (absent : findFunction context.program "calloc"=none) (sound : MemorySound context)
    (fit : size<2^64) (pure : SourcePure.CallFree count)
    (countEval : Eval context before count (.integer (integer64 size)) before)
    (actual : Eval context before (callocExpr count) value after) :
    (value=.null ∧ after=before) ∨
    (value=.pointer (wordPointer before.nextObject 0) ∧
      before.allocate .host (8*size) (PlatformMemory.zeroBytes (8*size))=
        some (⟨before.nextObject,0,.void⟩,after)) := by
  have expected : Args context before [count,.literal (.integer 8 "ULL")]
      [.integer (integer64 size),.integer (integer64 8)] before :=
    .ordered (List.Perm.refl _) (.cons countEval
      (.cons (.literal (.integer 8 "ULL") _ (.integer (integer64 8)) (by rfl)) .nil))
      (.cons rfl (.cons rfl .nil))
  cases actual with
  | cast ev converted =>
    cases ev with
    | call arguments called =>
      obtain ⟨_,middleEq,valuesEq⟩ := ApplicationPureCall.args_unique
        (by intro e member; simp only [List.mem_cons,List.mem_nil_iff,or_false] at member
            rcases member with rfl|rfl; exact pure; trivial) expected arguments
      rw [middleEq,←valuesEq] at called
      rcases calloc_call_cases absent sound fit called with failed | success
      · rcases failed with ⟨result,stateEq⟩
        cases result
        have eq : value=.null := by simpa [Value.convert] using converted.symm
        exact Or.inl ⟨eq,stateEq⟩
      · obtain ⟨pointer,result,born⟩ := success
        cases result
        unfold State.allocate at born
        split_ifs at born with occupied
        have pe := congrArg Prod.fst (Option.some.inj born)
        have se := congrArg Prod.snd (Option.some.inj born)
        dsimp only at pe se
        rw [←pe] at converted
        have eq : value=.pointer (wordPointer before.nextObject 0) := by
          simpa [Value.convert,wordPointer] using converted.symm
        exact Or.inr ⟨eq,by rw [←se];simp [State.allocate,occupied]⟩
    | load place _ => cases place
  | load place _ => cases place

/-- Every actual calloc/declaration creates either an initialized NULL local
or a local pointing to the actual fresh zero-byte object. No success premise. -/
theorem calloc_declaration_cases {F : Type} (context : Context F) {before after : State F}
    {count : Expr} {size : Nat} {cname : String} {flow : Flow}
    (absent : findFunction context.program "calloc"=none) (sound : MemorySound context)
    (well : WellScoped before) (host : before.mode=.host) (fit : size<2^64)
    (pure : SourcePure.CallFree count)
    (countEval : Eval context before count (.integer (integer64 size)) before)
    (actual : Exec context before (.declare (.pointer .u64) cname (some (callocExpr count))) flow after) :
    flow=.normal ∧ ∃object pointerId,
      after.environment=(cname,scalarPointer pointerId (.pointer .u64))::before.environment ∧
      Slot after pointerId before.scope (.pointer .u64) (nullablePointer object) ∧
      (∀id,object=some id → id=before.nextObject ∧
        after.objects id=some (zeroPrefixObject size 0)) ∧
      Frame before.nextObject before after [] ∧ after.scope=before.scope ∧
      before.nextObject≤pointerId ∧ pointerId<after.nextObject := by
  cases actual with
  | declareSome ev declared =>
    refine ⟨rfl,?_⟩
    rcases calloc_expression_cases context absent sound fit pure countEval ev with failed|success
    · rcases failed with ⟨rfl,stateEq⟩
      rw [stateEq] at declared
      have storage:=nullablePointer_storable none
      have d:=declare_storable storage storage.converted declared
      exact ⟨none,before.nextObject,d.environment,d.slot,by simp,
        declare_frame before.nextObject [] well (le_refl _) declared,d.scope,le_refl _,by rw [d.nextObject];omega⟩
    · rcases success with ⟨rfl,born⟩
      rename_i allocated
      have wa:=wellScoped_allocate well (by intro owner impossible;cases impossible) born
      have raw:=WordArrays.calloc_prefix_zero host born
      have af : Frame before.nextObject before allocated [] := by
        unfold State.allocate at born
        split_ifs at born with occupied
        cases Option.some.inj born
        exact ⟨wa,by simp,by simp,le_refl _,rfl,rfl,by intro id old _;simp [show id≠before.nextObject by omega]⟩
      have ae : allocated.environment=before.environment := by
        unfold State.allocate at born; split_ifs at born; cases Option.some.inj born; rfl
      have asc : allocated.scope=before.scope := by
        unfold State.allocate at born; split_ifs at born; cases Option.some.inj born; rfl
      have storage:=nullablePointer_storable (some before.nextObject)
      have d:=declare_storable storage storage.converted declared
      have bound:=wa.objectIds _ _ raw.2
      change before.nextObject<allocated.nextObject at bound
      refine ⟨some before.nextObject,allocated.nextObject,?_,?_,?_,
        af.trans (lower_cutoff (declare_frame allocated.nextObject [] wa (le_refl _) declared) af.nextObject),
        d.scope.trans asc,by omega,by rw [d.nextObject];omega⟩
      · rw [d.environment,ae]
      · simpa only [nullablePointer,asc] using d.slot
      · intro id same
        cases same
        exact ⟨rfl,(d.outside _ (by omega)).trans raw.2⟩

#print axioms calloc_expression_cases
#print axioms calloc_declaration_cases
end RH080Next.FFTPV.MainAllocation
