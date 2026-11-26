import FFTMainFailureView
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.MainAllocation
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings ApplicationBirthFrame

theorem NullableView.allocation_cons {F : Type} (context : Context F) {before after : State F}
    {n nId owner : Nat} {roles : List Role} {objects : Role → Option Nat} {ids : Role → Nat}
    {flow : Flow} {rest : List Stmt} (next : Role)
    (h : NullableView before n nId owner roles objects ids) (small : n≤2^24) (notBorn : next∉roles)
    (absent : findFunction context.program "calloc"=none) (sound : MemorySound context)
    (actual : ExecList context before (statement next::rest) flow after) :
    ∃middle object pointerId,
      NullableView middle n nId owner (next::roles) (Function.update objects next object)
        (Function.update ids next pointerId) ∧ Frame before.nextObject before middle [] ∧
      (∀id,object=some id → id=before.nextObject) ∧ ExecList context middle rest flow after := by
  cases actual with
  | cons head tail =>
    obtain ⟨_,object,pointerId,view,frame,fresh⟩ := h.birth_cases context next small notBorn absent sound head
    exact ⟨_,object,pointerId,view,frame,fresh,tail⟩
  | abrupt head abrupt =>
    have normal := (h.birth_cases context next small notBorn absent sound head).1
    exact False.elim (abrupt normal)

/-- Classification of every execution of the actual four calloc statements,
with all four independent generic allocation choices preserved. -/
theorem every_four_allocations {F : Type} (context : Context F) {before after : State F}
    {n nId owner : Nat} {flow : Flow}
    (nLookup : before.environment.lookup "n"=some (scalarPointer nId .u64))
    (nSlot : Slot before nId owner .u64 (.integer (integer64 n)))
    (well : WellScoped before) (host : before.mode=.host) (scope : before.scope=owner)
    (small : n≤2^24) (absent : findFunction context.program "calloc"=none) (sound : MemorySound context)
    (actual : ExecList context before allocationPrefix flow after) :
    flow=.normal ∧ ∃objects ids,
      NullableView after n nId owner [.output,.work,.twiddle,.data] objects ids ∧
      Frame before.nextObject before after [] ∧
      (∀r id,objects r=some id → before.nextObject ≤ id) := by
  have h0:=NullableView.initial nLookup nSlot well host scope
  obtain ⟨s1,o1,id1,h1,f1,fresh1,run1⟩ := h0.allocation_cons context .data small (by simp) absent sound actual
  obtain ⟨s2,o2,id2,h2,f2,fresh2,run2⟩ := h1.allocation_cons context .twiddle small (by simp) absent sound run1
  obtain ⟨s3,o3,id3,h3,f3,fresh3,run3⟩ := h2.allocation_cons context .work small (by simp) absent sound run2
  obtain ⟨last,o4,id4,h4,f4,fresh4,run4⟩ := h3.allocation_cons context .output small (by simp) absent sound run3
  cases run4
  have c2:=f1.trans (lower_cutoff f2 f1.nextObject)
  have c3:=c2.trans (lower_cutoff f3 c2.nextObject)
  refine ⟨rfl,_,_,h4,c3.trans (lower_cutoff f4 c3.nextObject),?_⟩
  intro r id someId
  have b1:=f1.nextObject
  have b2:=c2.nextObject
  have b3:=c3.nextObject
  cases r with
  | data => simp only [Function.update_apply] at someId; simp at someId; have := fresh1 id someId;omega
  | twiddle => simp only [Function.update_apply] at someId; simp at someId; have := fresh2 id someId;omega
  | work => simp only [Function.update_apply] at someId; simp at someId; have := fresh3 id someId;omega
  | output => simp only [Function.update_apply] at someId; simp at someId; have := fresh4 id someId;omega

#print axioms NullableView.allocation_cons
#print axioms every_four_allocations
end RH080Next.FFTPV.MainAllocation
