/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTMainParameter
import FFTRecursiveSegments
import FFTRecursiveIndexExpressions
import FFTFixedMultiplyParameters
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.MainRootBirth
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings ApplicationBirthFrame
open MainAllocation

inductive PointerVar where | root | temp | total | quad deriving DecidableEq

def pointerName : PointerVar → String | .root=>"root" | .temp=>"temp" | .total=>"total" | .quad=>"quad"
def pointerOffset : PointerVar → Nat | .root=>128 | .temp=>160 | .total=>192 | .quad=>208
def pointerType (_ : PointerVar) : CType:=.pointer .u64
def pointerIds (base : Nat) : PointerVar → Nat | .root=>base | .temp=>base+1 | .total=>base+2 | .quad=>base+3
def pointerValue (workObject : Nat) (p : PointerVar) : Value:=.pointer (wordPointer workObject (pointerOffset p))
def pointerStatement (p : PointerVar) : Stmt:=.declare (.pointer .u64) (pointerName p)
  (some (RecursiveSource.pointerOffset "work" (pointerOffset p)))
def pointerStatements : List Stmt:=[pointerStatement .root,pointerStatement .temp,pointerStatement .total,pointerStatement .quad]

theorem actual_w4_pointer_births : ((bodyItems FFTRecursivePV.w4_recursive_norm_upper_ast).drop 12).take 4=pointerStatements := by rfl
theorem actual_fap_pointer_births : ((bodyItems FapFFTRecursivePV.fap_recursive_norm_upper_ast).drop 12).take 4=pointerStatements := by rfl

abbrev RootVar:=Sum MainVar PointerVar
def localName : RootVar → String:=Sum.elim variableName pointerName
def localType : RootVar → CType:=Sum.elim variableType pointerType
def localIds (nId : Nat) (oldIds : Role → Nat) (base : Nat) : RootVar → Nat:=Sum.elim (variableId nId oldIds) (pointerIds base)
def localValue (n : Nat) (objects : Role → Nat) : RootVar → Value:=Sum.elim (variableValue n objects) (pointerValue (objects .work))
abbrev FullVar:=Option RootVar
def fullName : FullVar → String | none=>"status" | some v=>localName v
def fullType : FullVar → CType | none=>.u64 | some v=>localType v
def fullIds (nId : Nat) (oldIds : Role → Nat) (base status : Nat) : FullVar → Nat
  | none=>status | some v=>localIds nId oldIds base v
def fullValue (n : Nat) (objects : Role → Nat) : FullVar → Value
  | none=>.integer (integer64 0) | some v=>localValue n objects v

abbrev FullMainLocals {F : Type} (state : State F) (n nId owner : Nat) (objects oldIds : Role → Nat) (base status : Nat) :=
  Locals state fullName fullType (fullIds nId oldIds base status) owner (fullValue n objects)

private theorem old_name_different (v : MainVar) (p : PointerVar) : variableName v≠pointerName p := by
  cases v with
  | none=>cases p <;> decide
  | some r=>cases r <;> cases p <;> decide

/-- The real pointer RHS is evaluated from the actual work pointer and its
live typed allocation. It does not assume an initialized local pointer. -/
theorem pointer_eval {F : Type} (context : Context F) {state : State F}
    {n nId owner : Nat} {objects oldIds : Role → Nat} {data : Nat → Nat}
    (locals : Locals state variableName variableType (variableId nId oldIds) owner (variableValue n objects))
    (work : WordArrayRep state (objects .work) 512 data) (p : PointerVar) :
    Eval context state (RecursiveSource.pointerOffset "work" (pointerOffset p)) (pointerValue (objects .work) p) state := by
  have offsetBound : pointerOffset p<512 := by cases p <;> decide
  apply Eval.paren
  apply Eval.binaryLR (.variable (locals.lookup (some .work)) (locals.read (some .work)))
    (.literal (.integer (pointerOffset p) "ULL") _ (.integer (integer64 (pointerOffset p))) (by cases p <;> rfl))
  simpa only [variableValue,binary,pointerValue,Nat.zero_add,Option.map_some] using
    congrArg (Option.map Value.pointer) (slice_pointer_add work (start:=0) (i:=pointerOffset p) (by omega))

/-- Four actual pointer declarations introduce four fresh slots while all
preexisting main locals and all four typed zero allocations persist. -/
theorem pointer_births {F : Type} (context : Context F) {before : State F}
    {n nId owner : Nat} {objects oldIds : Role → Nat}
    (h : InitializedView before n nId owner objects oldIds [.work,.twiddle,.data,.output]) :
    ∃after,RecursiveSource.NormalSegment context before pointerStatements after ∧
      Locals after localName localType (localIds nId oldIds before.nextObject) owner (localValue n objects) ∧
      (∀r,WordArrayRep after (objects r) (length n r) (fun _=>0)) ∧
      Frame before.nextObject before after [] ∧ after.scope=owner := by
  have arrays:=initialized_words h
  have sa:=MultiplyParameters.pointer_storable (objects .work) 128
  obtain ⟨aState,aDeclared⟩:=ZeroFrame.declare_exists h.well (.pointer .u64) "root" _ sa
  have da:=declare_storable sa sa.converted aDeclared
  have wa:=wellScoped_declare h.well aDeclared
  have la:=locals_declare_old h.well h.locals (fun v=>old_name_different v .root) da
  have arraysA:=fun r=>array_declare_old h.well (arrays r) da
  have sb:=MultiplyParameters.pointer_storable (objects .work) 160
  obtain ⟨bState,bDeclared⟩:=ZeroFrame.declare_exists wa (.pointer .u64) "temp" _ sb
  have db:=declare_storable sb sb.converted bDeclared
  have wb:=wellScoped_declare wa bDeclared
  have lb:=locals_declare_old wa la (fun v=>old_name_different v .temp) db
  have arraysB:=fun r=>array_declare_old wa (arraysA r) db
  have sc:=MultiplyParameters.pointer_storable (objects .work) 192
  obtain ⟨cState,cDeclared⟩:=ZeroFrame.declare_exists wb (.pointer .u64) "total" _ sc
  have dc:=declare_storable sc sc.converted cDeclared
  have wc:=wellScoped_declare wb cDeclared
  have lc:=locals_declare_old wb lb (fun v=>old_name_different v .total) dc
  have arraysC:=fun r=>array_declare_old wb (arraysB r) dc
  have sd:=MultiplyParameters.pointer_storable (objects .work) 208
  obtain ⟨after,dDeclared⟩:=ZeroFrame.declare_exists wc (.pointer .u64) "quad" _ sd
  have dd:=declare_storable sd sd.converted dDeclared
  have wd:=wellScoped_declare wc dDeclared
  have ld:=locals_declare_old wc lc (fun v=>old_name_different v .quad) dd
  have arraysD:=fun r=>array_declare_old wc (arraysC r) dd
  have aB:=slot_declare_old wa da.slot db
  have aC:=slot_declare_old wb aB dc
  have aD:=slot_declare_old wc aC dd
  have bC:=slot_declare_old wb db.slot dc
  have bD:=slot_declare_old wc bC dd
  have cD:=slot_declare_old wc dc.slot dd
  have pointers : Locals after pointerName pointerType (pointerIds before.nextObject) owner (pointerValue (objects .work)) := by
    refine ⟨?_,?_,?_,?_⟩
    · intro p;cases p <;> rw [dd.environment,dc.environment,db.environment,da.environment] <;>
        simp [pointerName,pointerIds,pointerType,da.nextObject,db.nextObject,dc.nextObject,List.lookup,Nat.add_assoc]
    · intro p;cases p
      · simpa only [pointerType,pointerValue,pointerOffset,pointerIds,h.scope] using aD
      · simpa only [pointerType,pointerValue,pointerOffset,pointerIds,da.nextObject,da.scope,h.scope] using bD
      · simpa only [pointerType,pointerValue,pointerOffset,pointerIds,db.nextObject,da.nextObject,db.scope,da.scope,h.scope,Nat.add_assoc] using cD
      · simpa only [pointerType,pointerValue,pointerOffset,pointerIds,dc.nextObject,db.nextObject,da.nextObject,dc.scope,db.scope,da.scope,h.scope,Nat.add_assoc] using dd.slot
    · intro p q eq;cases p <;> cases q <;> simp_all [pointerIds] <;> omega
    · exact ld.bound
  have combined : Locals after localName localType (localIds nId oldIds before.nextObject) owner (localValue n objects) := by
    refine ⟨?_,?_,?_,ld.bound⟩
    · intro v;cases v with
      | inl v=>exact ld.lookup v
      | inr p=>exact pointers.lookup p
    · intro v;cases v with
      | inl v=>exact ld.slots v
      | inr p=>exact pointers.slots p
    · intro a b same
      cases a with
      | inl a=>
        cases b with
        | inl b=>exact congrArg Sum.inl (ld.distinct same)
        | inr b=>
          have old:=h.well.objectIds _ _ (h.locals.slots a).object
          cases b <;> simp [localIds,pointerIds] at same <;> omega
      | inr a=>
        cases b with
        | inl b=>
          have old:=h.well.objectIds _ _ (h.locals.slots b).object
          cases a <;> simp [localIds,pointerIds] at same <;> omega
        | inr b=>exact congrArg Sum.inr (pointers.distinct same)
  have fa:=declare_frame before.nextObject [] h.well (le_refl _) aDeclared
  have fb:=declare_frame before.nextObject [] wa fa.fresh bDeclared
  have fc:=declare_frame before.nextObject [] wb fb.fresh cDeclared
  have fd:=declare_frame before.nextObject [] wc fc.fresh dDeclared
  have run : ExecList context before pointerStatements .normal after :=
    .cons (.declareSome (pointer_eval context h.locals (arrays .work) .root) aDeclared)
      (.cons (.declareSome (pointer_eval context la (arraysA .work) .temp) bDeclared)
        (.cons (.declareSome (pointer_eval context lb (arraysB .work) .total) cDeclared)
          (.cons (.declareSome (pointer_eval context lc (arraysC .work) .quad) dDeclared) .nil)))
  have pure : ∀s∈pointerStatements,PureDeterminism.Simple s := by
    intro s hs
    simp only [pointerStatements,List.mem_cons,List.mem_nil_iff,or_false] at hs
    rcases hs with rfl|rfl|rfl|rfl <;> trivial
  exact ⟨after,.pure run pure,combined,arraysD,((fa.trans fb).trans fc).trans fd,
    dd.scope.trans (dc.scope.trans (db.scope.trans (da.scope.trans h.scope)))⟩

#print axioms pointer_births
end RH080Next.FFTPV.MainRootBirth
