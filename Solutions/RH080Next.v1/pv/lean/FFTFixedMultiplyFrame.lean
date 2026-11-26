/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTFixedMultiplyTotal
import FFTFixedMultiplyBeginFrame
import FFTFixedMultiplySuffixTotalFrame
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.MultiplyCall
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings ApplicationBirthFrame

structure CallerFrame {F : Type} (before after : State F) (writes : List Nat) : Prop where
  environment : after.environment=before.environment
  scope : after.scope=before.scope
  frame : Frame before.nextObject before after writes

private theorem append_exec {F : Type} {context : Context F} {before middle after : State F}
    {xs ys : List Stmt} {flow : Flow} (first : ExecList context before xs .normal middle)
    (second : ExecList context middle ys flow after) : ExecList context before (xs++ys) flow after:=by
  induction xs generalizing before with
  | nil=>cases first;exact second
  | cons x xs ih=>
    cases first with
    | cons run rest=>exact .cons run (ih rest)
    | abrupt run ne=>exact False.elim (ne rfl)

theorem fixed_multiply_call_framed {F : Type} (context : Context F)
    (selected : findFunction context.program "fixed_multiply"=some fixed_multiply_ast)
    (zeroSelected : findFunction context.program "zero_words"=some zero_words_ast)
    (incSelected : findFunction context.program "increment_words"=some increment_words_ast)
    (canonSelected : findFunction context.program "canonical_sign"=some FFTRecursivePV.canonical_sign_ast)
    (caller : State F)
    (outObj outSize outStart aObj aSize aStart bObj bSize bStart workObj workSize workStart : Nat)
    (old aData bData workData : Nat→Nat) (well : WellScoped caller)
    (outRep : WordArrayRep caller outObj outSize old)
    (work : WordArrayRep caller workObj workSize workData)
    (aRep : WordArrayRep caller aObj aSize aData) (bRep : WordArrayRep caller bObj bSize bData)
    (aShape : aObj=workObj → aSize=workSize) (bShape : bObj=workObj → bSize=workSize)
    (outShape : outObj=workObj → outSize=workSize)
    (aDisjoint : aObj≠workObj ∨ aStart+6≤workStart ∨ workStart+10≤aStart)
    (bDisjoint : bObj≠workObj ∨ bStart+6≤workStart ∨ workStart+10≤bStart)
    (outDisjoint : outObj≠workObj ∨ outStart+6≤workStart ∨ workStart+10≤outStart)
    (outBound : outStart+6≤outSize) (aBound : aStart+6≤aSize) (bBound : bStart+6≤bSize) (workBound : workStart+10≤workSize)
    (aDigits : ∀k,k<5 → aData (aStart+k)<1000000000)
    (bDigits : ∀k,k<5 → bData (bStart+k)<1000000000)
    (aBit : aData (aStart+5)≤1) (bBit : bData (bStart+5)≤1)
    (aSmall : FFT.Limbs.magnitude 1000000000 5 (fun k=>aData (aStart+k))≤1000*10^36)
    (bSmall : FFT.Limbs.magnitude 1000000000 5 (fun k=>bData (bStart+k))≤1000*10^36) :
    ∃after,Call context "fixed_multiply"
        [.pointer (wordPointer outObj outStart),.pointer (wordPointer aObj aStart),
          .pointer (wordPointer bObj bStart),.pointer (wordPointer workObj workStart)] caller
        (.value (.integer (integer64 0))) after ∧ CallerFrame caller after [outObj,workObj] := by
  let entry : State F:={caller.enterScope with environment:=[]}
  obtain ⟨entered,current,iId,data,binding,corePrefix,hp,params,product,readA,readB,oldFrame,beginFrame,enteredScope⟩:=
    MultiplyParameters.begin_execution_framed context zeroSelected caller outObj outStart aObj aSize aStart bObj bSize bStart
      workObj workSize workStart aData bData workData well work aRep bRep aShape bShape aDisjoint bDisjoint
      aBound bBound workBound aDigits bDigits
  obtain ⟨outData,outCurrent⟩:=MultiplyParameters.current_output_rep well outRep hp.work outShape oldFrame
  obtain ⟨aCurrent,ar,av⟩:=hp.aInput
  obtain ⟨bCurrent,br,bv⟩:=hp.bInput
  have bindings:=MultiplyParameters.suffix_bindings params hp
  have separate : ∀v,outObj≠MultiplyParameters.suffixIds (MultiplyParameters.ids entry.nextObject) iId v ∧
      workObj≠MultiplyParameters.suffixIds (MultiplyParameters.ids entry.nextObject) iId v:=by
    intro v
    exact ⟨MultiplyParameters.array_slot_different outCurrent (bindings.slots v),
      MultiplyParameters.array_slot_different hp.work (bindings.slots v)⟩
  have shape : workObj=outObj → workSize=outSize:=fun eq=>(outShape eq.symm).symm
  obtain ⟨middle,suffix,finalRep,suffixFrame⟩:=MultiplySuffix.suffix_framed context incSelected canonSelected bindings hp.well
    outCurrent ar br hp.work separate shape outDisjoint outBound aBound bBound workBound hp.workDigits
  let sign:=MultiplySuffix.signBit (aCurrent (aStart+5)) (bCurrent (bStart+5))
  obtain ⟨top,safe⟩:=MultiplyBounds.bounded_product (fun k=>aData (aStart+k)) (fun k=>bData (bStart+k))
    (fun k=>data (workStart+k)) product aSmall bSmall hp.workDigits
  have zeroStatus : MultiplySuffix.finalStatus outData data outStart workStart sign=0:=
    MultiplySuffix.finalStatus_eq_zero outData data outStart workStart sign top safe
  rw [zeroStatus] at suffix
  have whole : ExecList context entered functionStatements (.returned (.integer (integer64 0))) middle:=by
    have combined:=append_exec corePrefix suffix
    have suffixActual : (ProductRow.items fixed_multiply_ast.body).drop 3=MultiplySuffix.statements:=by rfl
    rw [←suffixActual,List.take_append_drop] at combined
    exact combined
  let after : State F:={middle.leaveScope entered.scope caller.environment with scope:=caller.scope}
  have called : Call context "fixed_multiply"
      [.pointer (wordPointer outObj outStart),.pointer (wordPointer aObj aStart),
        .pointer (wordPointer bObj bStart),.pointer (wordPointer workObj workStart)] caller
      (.value (.integer (integer64 0))) after:=by
    apply Call.internal (function:=fixed_multiply_ast) (entered:=entered) (middle:=middle)
      selected (by rfl) binding
    · exact Body.finish whole (by intro label impossible;cases impossible)
    · exact convert64 0 (by norm_num)
    · rfl
  have iFresh : caller.nextObject ≤ iId:=by
    by_contra no
    have old : iId < caller.nextObject:=by omega
    have different : iId≠workObj:=(hp.separate ProductOuter.PVar.i).1.symm
    have slot:=(hp.locals.slots ProductOuter.PVar.i).object
    have same:=oldFrame iId old different
    change current.objects iId=some (scalarObject entry.scope _ _) at slot
    rw [same] at slot
    have bad:=well.automatic iId _ caller.nextScope slot (by rfl)
    omega
  have beforeFrame : Frame caller.nextObject caller current [outObj,workObj]:=by
    refine ⟨beginFrame.well,beginFrame.fresh,beginFrame.nextObject,beginFrame.nextScope,beginFrame.mode,beginFrame.foreign,?_⟩
    intro id old outside
    exact beginFrame.outside id old (by
      intro member
      have equal : id=workObj:=by simpa only [List.mem_singleton] using member
      exact outside (by simp [equal]))
  have tailFrame : Frame caller.nextObject current middle [outObj,workObj]:=by
    refine ⟨suffixFrame.well,beginFrame.nextObject.trans suffixFrame.fresh,suffixFrame.nextObject,
      suffixFrame.nextScope,suffixFrame.mode,suffixFrame.foreign,?_⟩
    intro id old outside
    apply suffixFrame.outside id (old.trans_le beginFrame.nextObject)
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at outside ⊢
    exact ⟨outside.1,by change id≠iId;omega⟩
  have bodyFrame:=beforeFrame.trans tailFrame
  have restored : CallerFrame caller after [outObj,workObj]:=by
    refine ⟨rfl,rfl,?_,bodyFrame.fresh,bodyFrame.nextObject,bodyFrame.nextScope,bodyFrame.mode,bodyFrame.foreign,?_⟩
    · apply wellScoped_scope (wellScoped_leave bodyFrame.well entered.scope caller.environment)
      have current:=well.current
      have mono:=bodyFrame.nextScope
      change caller.scope < middle.nextScope
      omega
    · intro id old outside
      change (middle.objects id).map _=caller.objects id
      rw [bodyFrame.outside id old outside]
      cases present : caller.objects id with
      | none=>rfl
      | some object=>
        have different : object.storage≠.automatic entered.scope:=by
          intro equal
          rw [enteredScope] at equal
          have bad:=well.automatic id object caller.nextScope present equal
          omega
        simp [different]
  exact ⟨after,called,restored⟩

#print axioms fixed_multiply_call_framed
end RH080Next.FFTPV.MultiplyCall
