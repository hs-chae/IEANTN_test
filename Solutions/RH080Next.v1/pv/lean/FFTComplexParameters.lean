/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTStatusCall
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.ComplexSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings ApplicationBirthFrame

abbrev PVar:=MultiplyParameters.Var
abbrev pName:=MultiplyParameters.name
abbrev pType:=MultiplyParameters.type
abbrev pValue:=MultiplyParameters.value
abbrev pIds:=MultiplyParameters.ids

def statusDeclaration : Stmt:=.declare .u64 "status" (some (.literal (.integer 0 "ULL")))

theorem actual_parameters : complex_multiply_ast.parameters=fixed_multiply_ast.parameters:=by rfl

theorem actual_status : (ProductRow.items complex_multiply_ast.body).head?=some statusDeclaration:=by rfl

private theorem declarations_foreign {F : Type} {before after : State F}
    (run : Declarations before after) : after.foreign=before.foreign:=by
  induction run with
  | nil state=>rfl
  | cons first rest ih=>exact ih.trans (declare_foreign first)

/-- The actual complex helper begins with real four-pointer parameter binding
and a real zero-valued automatic status declaration, from an arbitrary caller.
The application arrays are not assumed initialized by this theorem. -/
theorem initialize_call {F : Type} (context : Context F) (caller : State F)
    (outObj outStart aObj aStart bObj bStart workObj workStart : Nat) (well : WellScoped caller) :
    let entry : State F:={caller.enterScope with environment:=[]}
    ∃entered after statusId,
      bindParameters entry complex_multiply_ast.parameters
        [.pointer (wordPointer outObj outStart),.pointer (wordPointer aObj aStart),
          .pointer (wordPointer bObj bStart),.pointer (wordPointer workObj workStart)]=some entered ∧
      Exec context entered statusDeclaration .normal after ∧
      Locals after pName pType (pIds entry.nextObject) entry.scope
        (pValue outObj outStart aObj aStart bObj bStart workObj workStart) ∧
      after.environment.lookup "status"=some (scalarPointer statusId .u64) ∧
      Slot after statusId entry.scope .u64 (.integer (integer64 0)) ∧
      Frame caller.nextObject caller after [] ∧ entered.scope=entry.scope ∧
      statusId=caller.nextObject+4 := by
  dsimp only
  let entry : State F:={caller.enterScope with environment:=[]}
  have we : WellScoped entry:=wellScoped_environment (wellScoped_enter well) []
  obtain ⟨entered,bound,params,chain,pwell,pno,pscope,pns⟩:=MultiplyParameters.initialize_parameters
    outObj outStart aObj aStart bObj bStart workObj workStart we rfl
  obtain ⟨after,declared⟩:=ZeroFrame.declare_exists pwell .u64 "status" (.integer (integer64 0))
    (ZeroFrame.u64_storable 0 (by norm_num))
  have ds : Declaration entered after "status" .u64 (.integer (integer64 0)):=
    declare_storable (ZeroFrame.u64_storable 0 (by norm_num)) (by rfl) declared
  have oldParams : Locals after pName pType (pIds entry.nextObject) entry.scope
      (pValue outObj outStart aObj aStart bObj bStart workObj workStart):=
    locals_declare_old pwell params (by intro v;cases v <;> decide) ds
  have fields:=chain.fields
  have parameterFrame : Frame caller.nextObject caller entered []:=by
    refine ⟨pwell,fields.1,fields.1,?_,fields.2.2.2.1,(declarations_foreign chain).trans (show entry.foreign=caller.foreign from rfl),?_⟩
    · rw [pns]
      change caller.nextScope≤caller.nextScope+1
      omega
    · intro id old absent
      exact fields.2.2.2.2 id old
  have localFrame : Frame caller.nextObject entered after []:=
    ApplicationBirthFrame.declare_frame caller.nextObject [] pwell fields.1 declared
  refine ⟨entered,after,entered.nextObject,?_,?_,oldParams,?_,?_,parameterFrame.trans localFrame,pscope,?_⟩
  · simpa only [actual_parameters] using bound
  · exact .declareSome (.literal (.integer 0 "ULL") _ (.integer (integer64 0)) (by rfl)) declared
  · rw [ds.environment]
    simp [List.lookup]
  · rw [←pscope]
    exact ds.slot
  · exact pno

#print axioms initialize_call
end RH080Next.FFTPV.ComplexSource
