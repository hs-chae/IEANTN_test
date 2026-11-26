/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTMainRootBirthBase
import ExplicitFFTRootSource
import FFTStatusCall
import FFTComplexFrame
import FFTComplexCorrect
import FFTRecursiveBindingsFrame
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
namespace RH080Next.FFTPV.MainRootBirth
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings ApplicationBirthFrame
open MainAllocation

def rootArguments : List Expr:=[.variable "root",.variable "n",.variable "work"]
def statusBirth : Stmt:=.declare .u64 "status" (some (.call "initialize_root" rootArguments))
def rootBirthStatements : List Stmt:=pointerStatements++[statusBirth]

theorem actual_w4_root_births : ((bodyItems FFTRecursivePV.w4_recursive_norm_upper_ast).drop 12).take 5=rootBirthStatements := by rfl
theorem actual_fap_root_births : ((bodyItems FapFFTRecursivePV.fap_recursive_norm_upper_ast).drop 12).take 5=rootBirthStatements := by rfl

def data (workData : Nat → Nat) : Role → Nat → Nat | .work=>workData | _=>fun _=>0

/-- Actual complete main locals through the root initializer, with numerical
root facts derived from the true source Call and physical typed-array frames. -/
structure Ready {F : Type} (state : State F) (n nId owner : Nat) (objects oldIds : Role → Nat)
    (base status : Nat) (workData : Nat → Nat) : Prop where
  locals : FullMainLocals state n nId owner objects oldIds base status
  arrays : ∀r,WordArrayRep state (objects r) (length n r) (data workData r)
  distinct : Function.Injective objects
  rootReal : RootSource.FixedValue workData 128 (RootSource.taylorState n 10).cr
  rootImag : RootSource.FixedValue workData 134 (-(RootSource.taylorState n 10).sr)
  rootValue : ComplexSource.pair workData 128=FFT.IntegerModel.root n
  workOutside : ∀k,k<512 → 80≤k → (k<128 ∨ 140≤k) → workData k=0
  well : WellScoped state
  scope : state.scope=owner

private theorem local_not_status (v : RootVar) : localName v≠"status" := by
  cases v with
  | inl v=>cases v with
    | none=>decide
    | some r=>cases r <;> decide
  | inr p=>cases p <;> decide

/-- Main instructions12..16 run their actual four declarations and actual
initialize_root Call. The real status slot is allocated after the callee has
returned, using its then-current object clock. Every allowed execution agrees. -/
theorem from_initialized {F : Type} (context : Context F) (functions : RootSource.Functions context)
    (selected : findFunction context.program "initialize_root"=some initialize_root_ast)
    {before : State F} {n nId owner : Nat} {objects oldIds : Role → Nat}
    (h : InitializedView before n nId owner objects oldIds [.work,.twiddle,.data,.output])
    (grid : RootSource.OriginalGrid n) :
    ∃after status workData,RecursiveSource.NormalSegment context before rootBirthStatements after ∧
      Ready after n nId owner objects oldIds before.nextObject status workData ∧
      Frame before.nextObject before after [objects .work] := by
  obtain ⟨pointerAfter,pointers,locals,arrays,pointerFrame,pointerScope⟩:=pointer_births context h
  let input:=RootSource.originalInput (objects .work) (fun _=>0) n grid
  obtain ⟨rootAfter,workData,called,every,rootWords,rootReal,rootImag,rootValue,rootFrame,rootOutside⟩:=
    RootSource.initialize_root_total context functions selected pointerAfter input grid pointerFrame.well (arrays .work)
  have fullFrame : MultiplyCall.CallerFrame pointerAfter rootAfter [objects .work] := by
    refine ⟨rootFrame.environment,rootFrame.scope,rootFrame.well,rootFrame.nextObject,
      rootFrame.nextObject,rootFrame.nextScope,rootFrame.mode,rootFrame.foreign,?_⟩
    intro id old absent
    exact rootFrame.objects id old (by simpa [input,RootSource.originalInput,RootSource.originalLayout] using absent)
  have rootLocals : Locals rootAfter localName localType (localIds nId oldIds before.nextObject) owner (localValue n objects) := by
    refine ⟨?_,?_,locals.distinct,locals.bound.trans_le fullFrame.frame.nextScope⟩
    · rw [fullFrame.environment];exact locals.lookup
    · intro v
      apply ComplexSource.slot_after_call pointerFrame.well (locals.slots v) fullFrame
      have ne:=RecursiveSource.array_ne_slot (arrays .work) (locals.slots v)
      simpa using ne.symm
  have arraysRoot : ∀r,WordArrayRep rootAfter (objects r) (length n r) (data workData r) := by
    intro r
    cases r with
    | work=>exact rootWords
    | data=>
      apply ComplexSource.word_array_after_call pointerFrame.well (arrays .data) fullFrame
      have ne : objects .data≠objects .work := by intro same;have impossible:=h.distinct same;cases impossible
      simpa using ne
    | output=>
      apply ComplexSource.word_array_after_call pointerFrame.well (arrays .output) fullFrame
      have ne : objects .output≠objects .work := by intro same;have impossible:=h.distinct same;cases impossible
      simpa using ne
    | twiddle=>
      apply ComplexSource.word_array_after_call pointerFrame.well (arrays .twiddle) fullFrame
      have ne : objects .twiddle≠objects .work := by intro same;have impossible:=h.distinct same;cases impossible
      simpa using ne
  have args : Args context pointerAfter rootArguments (RootSource.arguments input) pointerAfter := by
    apply Args.ordered (List.Perm.refl _)
    · exact .cons (.variable (locals.lookup (.inr .root)) (locals.read (.inr .root)))
        (.cons (.variable (locals.lookup (.inl none)) (locals.read (.inl none)))
          (.cons (.variable (locals.lookup (.inl (some .work))) (locals.read (.inl (some .work)))) .nil))
    · exact .cons rfl (.cons rfl (.cons rfl .nil))
  have storable:=ZeroFrame.u64_storable 0 (by norm_num)
  obtain ⟨after,declared⟩:=ZeroFrame.declare_exists fullFrame.frame.well .u64 "status" (.integer (integer64 0)) storable
  have d:=declare_storable storable storable.converted declared
  have callRun : Exec context pointerAfter statusBirth .normal after:=.declareSome (.call args called) declared
  have callEvery : ∀other flow,Exec context pointerAfter statusBirth flow other → flow=.normal ∧ other=after := by
    intro other flow run
    cases run with
    | declareSome ev dec=>
      obtain ⟨rfl,rfl⟩:=StatusCall.call_eval_unique (by simp [rootArguments,SourcePure.CallFree]) args every ev
      exact ⟨rfl,Option.some.inj (dec.symm.trans declared)⟩
  have fullLocals : FullMainLocals after n nId owner objects oldIds before.nextObject rootAfter.nextObject := by
    refine ⟨?_,?_,?_,?_⟩
    · intro v
      cases v with
      | none=>rw [d.environment];simp [fullName,fullType,fullIds,List.lookup]
      | some v=>
        rw [d.environment]
        simpa [fullName,fullType,fullIds,List.lookup,show (localName v=="status")=false by simp [local_not_status v]] using rootLocals.lookup v
    · intro v
      cases v with
      | none=>simpa only [fullType,fullIds,fullValue,fullFrame.scope,pointerScope] using d.slot
      | some v=>exact slot_declare_old fullFrame.frame.well (rootLocals.slots v) d
    · intro a b same
      cases a with
      | none=>
        cases b with
        | none=>rfl
        | some b=>
          have old:=fullFrame.frame.well.objectIds _ _ (rootLocals.slots b).object
          change rootAfter.nextObject=localIds nId oldIds before.nextObject b at same
          omega
      | some a=>
        cases b with
        | none=>
          have old:=fullFrame.frame.well.objectIds _ _ (rootLocals.slots a).object
          change localIds nId oldIds before.nextObject a=rootAfter.nextObject at same
          omega
        | some b=>exact congrArg some (rootLocals.distinct same)
    · rw [d.nextScope];exact rootLocals.bound
  have callFrame : Frame before.nextObject pointerAfter rootAfter [objects .work] :=
    ⟨fullFrame.frame.well,pointerFrame.fresh.trans fullFrame.frame.nextObject,fullFrame.frame.nextObject,
      fullFrame.frame.nextScope,fullFrame.frame.mode,fullFrame.frame.foreign,
      fun id old absent=>fullFrame.frame.outside id (old.trans_le pointerFrame.nextObject) absent⟩
  have statusFrame:=declare_frame before.nextObject [objects .work] fullFrame.frame.well callFrame.fresh declared
  have broadened : Frame before.nextObject before pointerAfter [objects .work] :=
    ⟨pointerFrame.well,pointerFrame.fresh,pointerFrame.nextObject,pointerFrame.nextScope,pointerFrame.mode,
      pointerFrame.foreign,fun id old _=>pointerFrame.outside id old (by simp)⟩
  have finalFrame:=(broadened.trans callFrame).trans statusFrame
  refine ⟨after,rootAfter.nextObject,workData,pointers.append (.single callRun callEvery),
    ⟨fullLocals,fun r=>array_declare_old fullFrame.frame.well (arraysRoot r) d,h.distinct,
      rootReal,rootImag,rootValue,?_,finalFrame.well,d.scope.trans (fullFrame.scope.trans pointerScope)⟩,finalFrame⟩
  intro k hk lo outside
  exact rootOutside k hk (by simpa [input,RootSource.originalInput,RootSource.originalLayout] using lo)
    (by simpa [input,RootSource.originalInput,RootSource.originalLayout] using outside)

#print axioms from_initialized
end RH080Next.FFTPV.MainRootBirth
