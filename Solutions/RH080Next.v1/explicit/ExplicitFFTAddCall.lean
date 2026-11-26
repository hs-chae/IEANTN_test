/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTAddCanonical
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.AddSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings
open FFT.Limbs
open IncrementSource (base)

theorem append_normal {F : Type} {context : Context F} {before middle after : State F}
    {xs ys : List Stmt} {flow : Flow} (first : ExecList context before xs .normal middle)
    (last : ExecList context middle ys flow after) : ExecList context before (xs++ys) flow after := by
  induction xs generalizing before with
  | nil=>cases first; exact last
  | cons x xs ih=>
    cases first with
    | cons run rest=>exact .cons run (ih rest)
    | abrupt run bad=>exact False.elim (bad rfl)

def arguments (input : Input) : List Value:=
  [.pointer (wordPointer (input.layout.object .out) (input.layout.start .out)),
   .pointer (wordPointer (input.layout.object .a) (input.layout.start .a)),
   .pointer (wordPointer (input.layout.object .b) (input.layout.start .b)),.integer (integer64 input.subtract)]

/-- Full genuine fixed_add source call, allowing out=a, out=b and supported
same-allocation disjoint slices. Every application-local initialization and
nested helper call is proved; no successful-effect premise is supplied. -/
theorem fixed_add_call {F : Type} (context : Context F)
    (selected : findFunction context.program "fixed_add"=some fixed_add_ast)
    (compareSelected : findFunction context.program "magnitude_compare"=some magnitude_compare_ast)
    (canonicalSelected : findFunction context.program "canonical_sign"=some FFTRecursivePV.canonical_sign_ast)
    (before : State F) (input : Input) (well : WellScoped before)
    (rep : ∀r,WordArrayRep before (input.layout.object r) (input.layout.length (input.layout.object r)) (input.old (input.layout.object r))) :
    ∃after,Call context "fixed_add" (arguments input) before (.value (.integer (integer64 (rawStatus input)))) after ∧
      WordArrayRep after (input.layout.object .out) (input.layout.length (input.layout.object .out)) (finalData input) ∧
      IncrementSource.FullCallerFrame before after (input.layout.object .out) := by
  let entry : State F:={before.enterScope with environment:=[]}
  have we : WellScoped entry:=wellScoped_environment (wellScoped_enter well) []
  obtain ⟨so,sa,sb,sp,sas,sbs,dout,da,db,dp,das,dbs,signRun,pre⟩:=initialize_signs context input we rfl rep
  have initial : Declarations entry sbs:=.cons dout (.cons da (.cons db (.cons dp (.cons das (.cons dbs (.nil sbs))))))
  have paramsOnly : Declarations entry sp:=.cons dout (.cons da (.cons db (.cons dp (.nil sp))))
  obtain ⟨flipped,flipRun,flippedPre,flipFrame⟩:=flip_sign_execution context pre
  have flipEffect:=SourceNoAlloc.exec_effect flipRun
    (by simp [flipBranch,flipTest,flipSign,SourceNoAlloc.Only,SourcePure.CallFree]) pre.well
  have flipScope : flipped.scope=entry.scope:=flipEffect.scope.trans initial.fields.2.1
  obtain ⟨sj,sc,returned,started,dj,dc,dCmp,compareFrame,startRun,views⟩:=
    initialize_loop_vars context compareSelected flippedPre flipScope
  have ij:=declare_storable (ZeroFrame.u64_storable 0 (by norm_num)) (convert64 0 (by norm_num)) dj
  have ic:=declare_storable (ZeroFrame.u64_storable 0 (by norm_num)) (convert64 0 (by norm_num)) dc
  have cmp64 : input.cmp < 2^64:=by have hb : input.cmp ≤ 2:=CompareSource.compareDigits_le_two _ _ _; omega
  have im:=declare_storable (ZeroFrame.u64_storable input.cmp cmp64) (convert64 input.cmp cmp64) dCmp
  have startScope : started.scope=entry.scope:=im.scope.trans (compareFrame.scope.trans (ic.scope.trans (ij.scope.trans flipScope)))
  obtain ⟨arithmetic,arithmeticRun,arithmeticPost,arithmeticFrame⟩:=arithmetic_execution context views
  have arithmeticScope : arithmetic.scope=entry.scope:=(arithmetic_scope arithmeticRun).2.trans startScope
  obtain ⟨finished,canonicalRun,post,canonicalFrame⟩:=canonical_execution context canonicalSelected arithmeticPost arithmeticScope
  have bodyTail : ExecList context started [arithmeticBranch,canonicalStatement,returnStatement]
      (.returned (.integer (integer64 (rawStatus input)))) finished:=
    .cons arithmeticRun (.cons canonicalRun (.abrupt
      (.returnSome (.variable (post.locals.lookup Var.carry) (post.locals.read Var.carry))) (by simp)))
  have bodyRun : ExecList context sp functionStatements (.returned (.integer (integer64 (rawStatus input)))) finished:=
    append_normal signRun (.cons flipRun (append_normal startRun bodyTail))
  have params : bindParameters entry fixed_add_ast.parameters (arguments input)=some sp := by
    change bindParameters entry [(.pointer .u64,"out"),(.pointer .u64,"a"),(.pointer .u64,"b"),(.u64,"subtract")]
      (arguments input)=some sp
    simp [bindParameters,arguments,dout,da,db,dp]
  let after : State F:={finished.leaveScope entry.scope before.environment with scope:=before.scope}
  have called : Call context "fixed_add" (arguments input) before (.value (.integer (integer64 (rawStatus input)))) after := by
    apply Call.internal (function:=fixed_add_ast) (entered:=sp) (middle:=finished) selected actual_body params
    · exact Body.finish bodyRun (by intro label he; cases he)
    · exact convert64 (rawStatus input) (lt_of_le_of_lt (rawStatus_bound input) (by norm_num))
    · simp only [after,paramsOnly.fields.2.1]
  have loopDecls : Declarations flipped sc:=.cons dj (.cons dc (.nil sc))
  have wf:=flippedPre.well
  have wj:=wellScoped_declare wf dj
  have wc:=wellScoped_declare wj dc
  have jSlot:=ApplicationBirthFrame.slot_declare_old wj ij.slot ic
  have jr:=slot_readonly wc jSlot compareFrame
  have boundReturned : flipped.nextObject < returned.nextObject:=compareFrame.well.objectIds _ _ jr.object
  have oldObjects : ∀id,id < before.nextObject → id≠input.layout.object .out → after.objects id=before.objects id := by
    intro id old different
    have oldEntry : id < entry.nextObject:=old
    have oldSign : id < sbs.nextObject:=lt_of_lt_of_le oldEntry initial.fields.1
    have oldFlip : id < flipped.nextObject:=by rw [flipEffect.nextObject]; exact oldSign
    have oldSc : id < sc.nextObject:=lt_of_lt_of_le oldFlip loopDecls.fields.1
    have oldR : id < returned.nextObject:=lt_trans oldFlip boundReturned
    have oldStarted : id < started.nextObject:=by rw [im.nextObject]; omega
    have oldArithmetic : id < arithmetic.nextObject:=lt_of_lt_of_le oldStarted arithmeticFrame.nextObject
    have notBs : id∉[preIds entry.nextObject PreVar.bsign]:=by simp only [List.mem_singleton,preIds]; change id≠before.nextObject+5; omega
    have absent : id∉writes input (fullIds (preIds entry.nextObject) flipped.nextObject returned.nextObject) := by
      have nj : id≠flipped.nextObject:=by omega
      have nc : id≠flipped.nextObject+1:=by omega
      simp [writes,fullIds,different,nj,nc]
    have initialSame : sbs.objects id=before.objects id:=initial.fields.2.2.2.2 id oldEntry
    have flippedSame : flipped.objects id=before.objects id:=(flipFrame.outside id oldSign notBs).trans initialSame
    have scSame : sc.objects id=before.objects id:=(loopDecls.fields.2.2.2.2 id oldFlip).trans flippedSame
    have returnedSame : returned.objects id=before.objects id:=(compareFrame.objects id oldSc).trans scSame
    have startedSame : started.objects id=before.objects id:=(im.outside id (by omega)).trans returnedSame
    have arithmeticSame : arithmetic.objects id=before.objects id:=(arithmeticFrame.outside id oldStarted absent).trans startedSame
    have finishedSame : finished.objects id=before.objects id:=(canonicalFrame.objects id oldArithmetic different).trans arithmeticSame
    change (finished.objects id).map _=before.objects id
    rw [finishedSame]
    cases present : before.objects id with
    | none=>rfl
    | some object=>
      have storage : object.storage≠.automatic entry.scope:=by
        intro bad
        have hb:=well.automatic id object before.nextScope present bad
        omega
      simp [storage]
  have afterWell : WellScoped after:=by
    apply wellScoped_scope (wellScoped_leave post.well entry.scope before.environment)
    have ho:=post.locals.bound
    have hb:=well.current
    change before.nextScope < finished.nextScope at ho
    change before.scope < finished.nextScope
    omega
  have initialForeign : sbs.foreign=entry.foreign:=
    (declare_foreign dbs).trans ((declare_foreign das).trans ((declare_foreign dp).trans
      ((declare_foreign db).trans ((declare_foreign da).trans (declare_foreign dout)))))
  have varsForeign : started.foreign=flipped.foreign:=
    (declare_foreign dCmp).trans (compareFrame.foreign.trans ((declare_foreign dc).trans (declare_foreign dj)))
  have foreign : after.foreign=before.foreign:=by
    change finished.foreign=entry.foreign
    exact canonicalFrame.foreign.trans (arithmeticFrame.foreign.trans
      (varsForeign.trans (flipEffect.foreign.trans initialForeign)))
  have nv : before.nextObject ≤ after.nextObject:=by
    have live:=post.well.objectIds _ _ (post.locals.slots Var.out).object
    change before.nextObject < finished.nextObject at live
    exact live.le
  have ns : before.nextScope ≤ after.nextScope:=by
    have live:=post.locals.bound
    change before.nextScope < finished.nextScope at live
    exact live.le
  exact ⟨after,called,IncrementSource.wordArray_leave post.array,
    ⟨rfl,rfl,foreign,afterWell,oldObjects⟩,nv,ns,post.array.1.trans (rep .out).1.symm⟩

#print axioms fixed_add_call
end RH080Next.FFTPV.AddSource
