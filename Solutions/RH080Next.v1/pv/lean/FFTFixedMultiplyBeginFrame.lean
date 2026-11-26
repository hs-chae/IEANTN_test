/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTFixedMultiplyBegin
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.MultiplyParameters
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings ApplicationBirthFrame

private theorem declarations_foreign {F : Type} {before after : State F}
    (chain : Declarations before after) : after.foreign=before.foreign := by
  induction chain with
  | nil state => rfl
  | cons declared tail ih => exact ih.trans (declare_foreign declared)

/-- Application entry is the actual C call entry, followed by four real
parameter declarations, real zero_words initialization, and all source product
loops. Caller arrays may occupy disjoint slices of one actual allocation. -/
theorem begin_execution_framed {F : Type} (context : Context F)
    (selected : findFunction context.program "zero_words"=some zero_words_ast) (caller : State F)
    (outObj outStart aObj aSize aStart bObj bSize bStart workObj workSize workStart : Nat)
    (aData bData workData : Nat→Nat) (well : WellScoped caller)
    (work : WordArrayRep caller workObj workSize workData)
    (aRep : WordArrayRep caller aObj aSize aData) (bRep : WordArrayRep caller bObj bSize bData)
    (aShape : aObj=workObj → aSize=workSize) (bShape : bObj=workObj → bSize=workSize)
    (aDisjoint : aObj≠workObj ∨ aStart+6≤workStart ∨ workStart+10≤aStart)
    (bDisjoint : bObj≠workObj ∨ bStart+6≤workStart ∨ workStart+10≤bStart)
    (aBound : aStart+6≤aSize) (bBound : bStart+6≤bSize) (workBound : workStart+10≤workSize)
    (aDigits : ∀k,k<5 → aData (aStart+k)<1000000000)
    (bDigits : ∀k,k<5 → bData (bStart+k)<1000000000) :
    let entry : State F:={caller.enterScope with environment:=[]}
    ∃entered after iId finalData,
      bindParameters entry fixed_multiply_ast.parameters
        [.pointer (wordPointer outObj outStart),.pointer (wordPointer aObj aStart),
          .pointer (wordPointer bObj bStart),.pointer (wordPointer workObj workStart)]=some entered ∧
      ExecList context entered ((ProductRow.items fixed_multiply_ast.body).take 3) .normal after ∧
      ProductOuter.View after aObj aSize aStart bObj bSize bStart workObj workSize workStart
        (coreIds (ids entry.nextObject) iId) (fun _=>entry.scope)
        (fun k=>aData (aStart+k)) (fun k=>bData (bStart+k)) finalData 5 ∧
      Locals after name type (ids entry.nextObject) entry.scope
        (value outObj outStart aObj aStart bObj bStart workObj workStart) ∧
      RH080Next.FFT.Limbs.value 1000000000 10 (fun k=>finalData (workStart+k))=
        RH080Next.FFT.Limbs.value 1000000000 5 (fun k=>aData (aStart+k))*
        RH080Next.FFT.Limbs.value 1000000000 5 (fun k=>bData (bStart+k)) ∧
      (∀k,k<6 → after.load (wordPointer aObj (aStart+k))=some (.integer (integer64 (aData (aStart+k))))) ∧
      (∀k,k<6 → after.load (wordPointer bObj (bStart+k))=some (.integer (integer64 (bData (bStart+k))))) ∧
      (∀id,id<caller.nextObject → id≠workObj → after.objects id=caller.objects id) ∧
      Frame caller.nextObject caller after [workObj] ∧ entered.scope=entry.scope := by
  dsimp only
  let entry : State F:={caller.enterScope with environment:=[]}
  have we : WellScoped entry:=wellScoped_environment (wellScoped_enter well) []
  obtain ⟨entered,bound,params,chain,pwell,pno,pscope,pns⟩:=initialize_parameters
    outObj outStart aObj aStart bObj bStart workObj workStart we rfl
  have fields:=chain.fields
  have wc:=well.objectIds _ _ work.2.1
  have ac:=well.objectIds _ _ aRep.2.1
  have bc:=well.objectIds _ _ bRep.2.1
  have workP : WordArrayRep entered workObj workSize workData:=
    ⟨fields.2.2.2.1.trans work.1,(fields.2.2.2.2 workObj wc).trans work.2.1,work.2.2⟩
  have aP : WordArrayRep entered aObj aSize aData:=
    ⟨fields.2.2.2.1.trans aRep.1,(fields.2.2.2.2 aObj ac).trans aRep.2.1,aRep.2.2⟩
  have bP : WordArrayRep entered bObj bSize bData:=
    ⟨fields.2.2.2.1.trans bRep.1,(fields.2.2.2.2 bObj bc).trans bRep.2.1,bRep.2.2⟩
  have separate : ∀v,workObj≠ids entry.nextObject v ∧ aObj≠ids entry.nextObject v ∧ bObj≠ids entry.nextObject v:=by
    intro v;cases v <;> simp only [ids] <;> change workObj≠_ ∧ aObj≠_ ∧ bObj≠_ <;> dsimp only [entry,State.enterScope] <;> omega
  have freshScope : entered.nextScope=entry.scope+1:=by rw [pns];rfl
  have latest : entered.nextObject=ids entry.nextObject Var.work+1:=by rw [pno];rfl
  obtain ⟨after,iId,finalData,run,ha,pa,frame,product,readA,readB⟩:=initialized_core_execution context selected pwell params
    pscope.symm latest freshScope workP aP bP aShape bShape aDisjoint bDisjoint aBound bBound workBound aDigits bDigits separate
  refine ⟨entered,after,iId,finalData,bound,?_,ha,pa,product,readA,readB,?_,?_,pscope⟩
  · simpa only [actual_initialized_core] using run
  · intro id old different
    rw [frame.outside id (old.trans_le fields.1) (by simp [different])]
    exact fields.2.2.2.2 id old

  · have parameterFrame : Frame caller.nextObject caller entered [workObj] := by
      refine ⟨pwell,fields.1,fields.1,?_,fields.2.2.2.1,(declarations_foreign chain).trans (show entry.foreign=caller.foreign from rfl),?_⟩
      · rw [pns]
        change caller.nextScope≤caller.nextScope+1
        omega
      · intro id old outside
        exact fields.2.2.2.2 id old
    have coreFrame : Frame caller.nextObject entered after [workObj] := by
      refine ⟨frame.well,fields.1.trans frame.nextObject,frame.nextObject,frame.nextScope,frame.mode,frame.foreign,?_⟩
      intro id old outside
      exact frame.outside id (old.trans_le fields.1) outside
    exact parameterFrame.trans coreFrame

#print axioms begin_execution_framed
end RH080Next.FFTPV.MultiplyParameters
