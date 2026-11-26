/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTRootStart
import ExplicitFFTRootLoop
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.RootSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings

def arguments (input : Input) : List Value:=[
  .pointer (wordPointer input.layout.object input.layout.rootStart),
  .integer (integer64 input.n),.pointer (wordPointer input.layout.object input.layout.workStart)]

/-- The complete actual initialize_root source call, from arbitrary caller
memory and real parameter allocation through all ten Taylor iterations and the
source's sign/canonical epilogue. It computes the existing integer root model
on exactly the two original grids and proves the full shared-allocation frame.
Every permitted source execution returns the same status and final state,
including all permitted argument and status-expression evaluation orders. -/
theorem initialize_root_call {F : Type} (context : Context F) (functions : Functions context)
    (selected : findFunction context.program "initialize_root"=some initialize_root_ast)
    (before : State F) (input : Input) (grid : OriginalGrid input.n) (well : WellScoped before)
    (rep : WordArrayRep before input.layout.object input.layout.size input.old) :
    ∃after finalData,Call context "initialize_root" (arguments input) before (.value (.integer (integer64 0))) after ∧
      EveryCall context before "initialize_root" (arguments input) (.value (.integer (integer64 0))) after ∧
      WordArrayRep after input.layout.object input.layout.size finalData ∧
      FixedValue finalData input.layout.rootStart (taylorState input.n 10).cr ∧
      FixedValue finalData (input.layout.rootStart+6) (-(taylorState input.n 10).sr) ∧
      (CanonicalSource.represented finalData input.layout.rootStart,CanonicalSource.represented finalData (input.layout.rootStart+6))=
        FFT.IntegerModel.root input.n ∧
      IncrementSource.FullCallerFrame before after input.layout.object ∧
      ∀k,k< input.layout.size → (k< input.layout.workStart ∨ input.layout.workStart+80≤ k) →
        (k< input.layout.rootStart ∨ input.layout.rootStart+12≤ k) → finalData k=input.old k := by
  let entry : State F:={before.enterScope with environment:=[]}
  have we : WellScoped entry:=wellScoped_environment (wellScoped_enter well) []
  obtain ⟨sr,sn,sw,dr,dn,dw,paramView⟩:=initialize_parameters input we rfl rep
  dsimp only [paramValue] at dr dn dw
  have declarations : Declarations entry sw:=.cons dr (.cons dn (.cons dw (.nil sw)))
  have paramScope : sw.scope=entry.scope:=declarations.fields.2.1
  obtain ⟨started,startData,statusId,indexId,startRun,startEvery,startRuntime,startValues,startFrame,startScope,startOutside⟩:=
    start_execution context functions paramView paramScope grid
  obtain ⟨looped,loopData,loopRun,loopEvery,loopRuntime,loopValues,loopFrame,loopScope,loopOutside⟩:=
    loop_execution context functions 10 (by omega) startRuntime startValues grid
  obtain ⟨finished,finalData,tailRun,tailEvery,tailView,cr,sinValue,rootValue,tailFrame,tailOutside⟩:=tail_execution context functions loopRuntime loopValues grid
  have bodyRun : ExecList context sw sourceStatements (.returned (.integer (integer64 0))) finished:=by
    rw [source_list_split]
    exact append_normal startRun (.cons loopRun tailRun)
  have bodyEvery : EveryList context sw sourceStatements (.returned (.integer (integer64 0))) finished:=by
    rw [source_list_split]
    exact every_append startEvery (every_cons loopEvery tailEvery)
  have params : bindParameters entry initialize_root_ast.parameters (arguments input)=some sw:=by
    change bindParameters entry [(.pointer .u64,"root"),(.u64,"n"),(.pointer .u64,"work")] (arguments input)=some sw
    simp [bindParameters,arguments,paramValue,dr,dn,dw]
  let after : State F:={finished.leaveScope entry.scope before.environment with scope:=before.scope}
  have called : Call context "initialize_root" (arguments input) before (.value (.integer (integer64 0))) after:=by
    apply Call.internal (function:=initialize_root_ast) (entered:=sw) (middle:=finished)
      selected actual_source_statements params
    · exact Body.finish bodyRun (by intro label impossible;cases impossible)
    · exact convert64 0 (by norm_num)
    · simp only [after,paramScope]
  have everyCalled : EveryCall context before "initialize_root" (arguments input) (.value (.integer (integer64 0))) after:=by
    apply every_call_from_body selected actual_source_statements (by intro bad;cases bad) params bodyEvery
      (by intro label;rfl) (convert64 0 (by norm_num))
    simp only [after,paramScope]
  have wr:=wellScoped_declare we dr
  have wn:=wellScoped_declare wr dn
  have birth0:=ApplicationBirthFrame.declare_frame entry.nextObject [input.layout.object] we (le_refl _) dr
  have birth1:=ApplicationBirthFrame.declare_frame entry.nextObject [input.layout.object] wr birth0.fresh dn
  have birth2:=ApplicationBirthFrame.declare_frame entry.nextObject [input.layout.object] wn birth1.fresh dw
  have paramFrame:=birth0.trans (birth1.trans birth2)
  have prefixFrame:=paramFrame.trans (lower_frame startFrame paramFrame.nextObject)
  have loopFrame' : ApplicationBirthFrame.Frame entry.nextObject started looped [input.layout.object]:=by
    simpa only [paramIds] using loopFrame
  have beforeTail:=prefixFrame.trans loopFrame'
  have wholeFrame:=beforeTail.trans (lower_frame (unary_frame tailFrame) beforeTail.nextObject)
  have enteredFrame : ApplicationBirthFrame.Frame before.nextObject before.enterScope finished [input.layout.object]:=
    ⟨wholeFrame.well,wholeFrame.fresh,wholeFrame.nextObject,wholeFrame.nextScope,wholeFrame.mode,wholeFrame.foreign,wholeFrame.outside⟩
  have callerFrame:=ApplicationBirthFrame.close_frame well (le_refl _) enteredFrame
  have fullFrame : IncrementSource.FullCallerFrame before after input.layout.object:=full_caller_frame rfl rfl callerFrame
  refine ⟨after,finalData,called,everyCalled,IncrementSource.wordArray_leave tailView.params.array,cr,sinValue,rootValue,fullFrame,?_⟩
  intro k hk hw hr
  exact (tailOutside k hr).trans ((loopOutside k hk hw hr).trans (startOutside k hk hw hr))

#print axioms initialize_root_call
end RH080Next.FFTPV.RootSource
