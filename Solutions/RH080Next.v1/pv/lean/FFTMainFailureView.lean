import FFTMainFailureAllocation
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.MainAllocation
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings ApplicationBirthFrame

/-- Actual declared pointers may independently be NULL or fresh allocations. -/
structure NullableView {F : Type} (state : State F) (n nId owner : Nat) (roles : List Role)
    (objects : Role → Option Nat) (ids : Role → Nat) : Prop where
  nLookup : state.environment.lookup "n"=some (scalarPointer nId .u64)
  nSlot : Slot state nId owner .u64 (.integer (integer64 n))
  lookup : ∀r∈roles,state.environment.lookup (name r)=some (scalarPointer (ids r) (.pointer .u64))
  slots : ∀r∈roles,Slot state (ids r) owner (.pointer .u64) (nullablePointer (objects r))
  raw : ∀r∈roles,∀id,objects r=some id → state.objects id=some (zeroPrefixObject (length n r) 0)
  differentObjects : ∀r∈roles,∀s∈roles,∀id,objects r=some id → objects s=some id → r=s
  differentSlots : ∀r∈roles,∀s∈roles,ids r=ids s → r=s
  nSeparate : ∀r∈roles,nId≠ids r
  well : WellScoped state
  host : state.mode=.host
  scope : state.scope=owner

theorem NullableView.initial {F : Type} {state : State F} {n nId owner : Nat}
    (lookup : state.environment.lookup "n"=some (scalarPointer nId .u64))
    (slot : Slot state nId owner .u64 (.integer (integer64 n)))
    (well : WellScoped state) (host : state.mode=.host) (scope : state.scope=owner) :
    NullableView state n nId owner [] (fun _=>none) (fun _=>0) := by
  refine ⟨lookup,slot,?_,?_,?_,?_,?_,?_,well,host,scope⟩ <;> simp

theorem NullableView.count_eval {F : Type} (context : Context F) {state : State F}
    {n nId owner : Nat} {roles : List Role} {objects : Role → Option Nat} {ids : Role → Nat}
    (h : NullableView state n nId owner roles objects ids) (small : n≤2^24) (r : Role) :
    Eval context state (countExpr r) (.integer (integer64 (length n r))) state := by
  exact (View.initial h.nLookup h.nSlot h.well h.host h.scope).count_eval context small r

theorem countExpr_pure (r : Role) : SourcePure.CallFree (countExpr r) := by cases r <;> trivial

private theorem preserve_slot {F : Type} {before after : State F} {id owner : Nat}
    {ctype : CType} {value : Value} (well : WellScoped before)
    (slot : Slot before id owner ctype value) (frame : Frame before.nextObject before after []) :
    Slot after id owner ctype value :=
  ⟨slot.storable,(frame.outside id (well.objectIds _ _ slot.object) (by simp)).trans slot.object⟩

/-- All executions of a source allocation declaration preserve every older
pointer/raw allocation and record its actual allocation choice. -/
theorem NullableView.birth_cases {F : Type} (context : Context F) {before after : State F}
    {n nId owner : Nat} {roles : List Role} {objects : Role → Option Nat} {ids : Role → Nat}
    {flow : Flow} (next : Role) (h : NullableView before n nId owner roles objects ids)
    (small : n≤2^24) (notBorn : next∉roles)
    (absent : findFunction context.program "calloc"=none) (sound : MemorySound context)
    (actual : Exec context before (statement next) flow after) :
    flow=.normal ∧ ∃object pointerId,
      NullableView after n nId owner (next::roles) (Function.update objects next object)
        (Function.update ids next pointerId) ∧ Frame before.nextObject before after [] ∧
        (∀id,object=some id → id=before.nextObject) := by
  obtain ⟨normal,object,pointerId,environment,slot,raw,frame,scope,pointerLower,pointerUpper⟩ :=
    calloc_declaration_cases context absent sound h.well h.host
      (by have fit:=length_bytes_fit small next;omega) (countExpr_pure next)
      (h.count_eval context small next) actual
  have oldNe (r : Role) (member : r∈roles) : r≠next := by intro eq;exact notBorn (eq ▸ member)
  have objectBound (r : Role) (member : r∈roles) (id : Nat) (someId : objects r=some id) :
      id<before.nextObject := h.well.objectIds _ _ (h.raw r member id someId)
  have slotBound (r : Role) (member : r∈roles) : ids r<before.nextObject := h.well.objectIds _ _ (h.slots r member).object
  have nBound : nId<before.nextObject := h.well.objectIds _ _ h.nSlot.object
  refine ⟨normal,object,pointerId,⟨?_,preserve_slot h.well h.nSlot frame,?_,?_,?_,?_,?_,?_,
    frame.well,frame.mode.trans h.host,scope.trans h.scope⟩,frame,fun id same=>(raw id same).1⟩
  · have ne : name next≠"n" := by cases next <;> decide
    rw [environment]
    simpa [List.lookup,show ("n"==name next)=false by simp [Ne.symm ne]] using h.nLookup
  · intro r member
    rcases List.mem_cons.mp member with eq|old
    · subst r; simp [environment]
    · have ne:=oldNe r old
      have names : name r≠name next := by intro eq;exact ne (name_injective eq)
      rw [Function.update_of_ne ne,environment]
      simpa [List.lookup,show (name r==name next)=false by simp [names]] using h.lookup r old
  · intro r member
    rcases List.mem_cons.mp member with eq|old
    · subst r;simpa [h.scope] using slot
    · have ne:=oldNe r old
      rw [Function.update_of_ne ne,Function.update_of_ne ne]
      exact preserve_slot h.well (h.slots r old) frame
  · intro r member id someId
    rcases List.mem_cons.mp member with eq|old
    · subst r
      simp only [Function.update_self] at someId
      exact (raw id someId).2
    · have ne:=oldNe r old
      rw [Function.update_of_ne ne] at someId
      exact (frame.outside id (objectBound r old id someId) (by simp)).trans (h.raw r old id someId)
  · intro r rm s sm id hr hs
    rcases List.mem_cons.mp rm with rnew|rold
    · subst r
      rcases List.mem_cons.mp sm with snew|sold
      · exact snew.symm
      · rw [Function.update_self] at hr
        rw [Function.update_of_ne (oldNe s sold)] at hs
        have fresh:=(raw id hr).1
        have old:=objectBound s sold id hs
        omega
    · rcases List.mem_cons.mp sm with snew|sold
      · subst s
        rw [Function.update_self] at hs
        rw [Function.update_of_ne (oldNe r rold)] at hr
        have fresh:=(raw id hs).1
        have old:=objectBound r rold id hr
        omega
      · rw [Function.update_of_ne (oldNe r rold)] at hr
        rw [Function.update_of_ne (oldNe s sold)] at hs
        exact h.differentObjects r rold s sold id hr hs
  · intro r rm s sm same
    rcases List.mem_cons.mp rm with rnew|rold
    · subst r
      rcases List.mem_cons.mp sm with snew|sold
      · exact snew.symm
      · have ne:=oldNe s sold
        have bound:=slotBound s sold
        simp only [Function.update_self,Function.update_of_ne ne] at same
        omega
    · rcases List.mem_cons.mp sm with snew|sold
      · subst s
        have ne:=oldNe r rold
        have bound:=slotBound r rold
        simp only [Function.update_self,Function.update_of_ne ne] at same
        omega
      · rw [Function.update_of_ne (oldNe r rold),Function.update_of_ne (oldNe s sold)] at same
        exact h.differentSlots r rold s sold same
  · intro r member
    rcases List.mem_cons.mp member with eq|old
    · subst r;simp only [Function.update_self];omega
    · rw [Function.update_of_ne (oldNe r old)];exact h.nSeparate r old

/-- With no NULL pointers the nullable view becomes the existing exact raw
application view of this execution's state, without choosing another run. -/
theorem NullableView.nonnull_view {F : Type} {state : State F} {n nId owner : Nat}
    {roles : List Role} {objects : Role → Option Nat} {ids : Role → Nat}
    (h : NullableView state n nId owner roles objects ids)
    (nonnull : ∀r∈roles,objects r≠none) :
    View state n nId owner roles (fun r=>(objects r).getD 0) ids := by
  have someId (r : Role) (member : r∈roles) : objects r=some ((objects r).getD 0) := by
    cases eq:objects r with
    | none => exact False.elim (nonnull r member eq)
    | some id => rfl
  refine ⟨h.nLookup,h.nSlot,h.lookup,?_,?_,?_,h.differentSlots,h.nSeparate,h.well,h.host,h.scope⟩
  · intro r member
    have slot:=h.slots r member
    rw [someId r member] at slot
    exact slot
  · intro r member;exact h.raw r member _ (someId r member)
  · intro r rm s sm same
    exact h.differentObjects r rm s sm _ (someId r rm) (by rw [same];exact someId s sm)

#print axioms NullableView.birth_cases
#print axioms NullableView.nonnull_view
end RH080Next.FFTPV.MainAllocation
