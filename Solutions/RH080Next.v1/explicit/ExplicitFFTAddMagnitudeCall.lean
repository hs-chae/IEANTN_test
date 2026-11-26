/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTAddMagnitudeLoop
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.AddMagnitudeSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings
open RootSource

def arguments (input : Input) : List Value:=[.pointer (wordPointer input.layout.outObject input.layout.outStart),
  .pointer (wordPointer input.layout.aObject input.layout.aStart),.integer (integer64 input.layout.n)]
def functionStatements : List Stmt:=[.declare .u64 "i" (some (.literal (.integer 0 "ULL"))),
  .declare .u64 "carry" (some (.literal (.integer 0 "ULL"))),loop,.returnValue (some (.variable "carry"))]

theorem add_magnitude_call {F : Type} (context : Context F)
    (selected : findFunction context.program "add_magnitude"=some add_magnitude_ast)
    (before : State F) (input : Input) (well : WellScoped before)
    (outRep : WordArrayRep before input.layout.outObject (input.layout.length input.layout.outObject) (input.old input.layout.outObject))
    (aRep : WordArrayRep before input.layout.aObject (input.layout.length input.layout.aObject) (input.old input.layout.aObject)) :
    ∃after,Call context "add_magnitude" (arguments input) before (.value (.integer (integer64 (row input input.layout.n).2))) after ∧
      EveryCall context before "add_magnitude" (arguments input) (.value (.integer (integer64 (row input input.layout.n).2))) after ∧
      WordArrayRep after input.layout.outObject (input.layout.length input.layout.outObject) (currentData input input.layout.n) ∧
      IncrementSource.FullCallerFrame before after input.layout.outObject:=by
  let entry : State F:={before.enterScope with environment:=[]}
  have we : WellScoped entry:=wellScoped_environment (wellScoped_enter well) []
  obtain ⟨so,sa,sn,si,sc,dOut,da,dn,di,dc,h⟩:=initialize_parameters input we rfl outRep aRep
  have declarations : Declarations entry sc:=.cons dOut (.cons da (.cons dn (.cons di (.cons dc (.nil sc)))))
  have params : Declarations entry sn:=.cons dOut (.cons da (.cons dn (.nil sn)))
  have paramScope : sn.scope=entry.scope:=params.fields.2.1
  obtain ⟨finished,loopRun,post,loopFrame,loopScope⟩:=loop_execution context input.layout.n h (by intro v;cases v <;> simp [ids]) (by omega)
  have diRun : Exec context sn (.declare .u64 "i" (some (.literal (.integer 0 "ULL")))) .normal si:=.declareSome (.literal _ _ _ (by rfl)) di
  have dcRun : Exec context si (.declare .u64 "carry" (some (.literal (.integer 0 "ULL")))) .normal sc:=.declareSome (.literal _ _ _ (by rfl)) dc
  have returnRun : Exec context finished (.returnValue (some (.variable "carry"))) (.returned (.integer (integer64 (row input input.layout.n).2))) finished:=
    .returnSome (.variable (post.locals.lookup Var.carry) (post.locals.read Var.carry))
  have bodyRun : ExecList context sn functionStatements (.returned (.integer (integer64 (row input input.layout.n).2))) finished:=
    .cons diRun (.cons dcRun (.cons loopRun (.abrupt returnRun (by simp))))
  have bodyEvery : EveryList context sn functionStatements (.returned (.integer (integer64 (row input input.layout.n).2))) finished:=
    every_cons (every_pure (by trivial) diRun) (every_cons (every_pure (by trivial) dcRun)
      (every_cons (every_of_unique (loop_unique context) loopRun) (every_abrupt (every_pure (by trivial) returnRun) (by simp))))
  have parameters : bindParameters entry add_magnitude_ast.parameters (arguments input)=some sn:=by
    change bindParameters entry [(.pointer .u64,"out"),(.pointer .u64,"a"),(.u64,"n")] (arguments input)=some sn
    simp [bindParameters,arguments,dOut,da,dn]
  have carry64 : (row input input.layout.n).2<2^64:=by have h:=row_carry input input.layout.n (le_refl _);omega
  let after : State F:={finished.leaveScope entry.scope before.environment with scope:=before.scope}
  have called : Call context "add_magnitude" (arguments input) before (.value (.integer (integer64 (row input input.layout.n).2))) after:=by
    apply Call.internal (function:=add_magnitude_ast) (entered:=sn) (middle:=finished) selected actual_body parameters
    · exact Body.finish bodyRun (by intro label impossible;cases impossible)
    · exact convert64 _ carry64
    · simp only [after,paramScope]
  have everyCalled : EveryCall context before "add_magnitude" (arguments input) (.value (.integer (integer64 (row input input.layout.n).2))) after:=by
    apply every_call_from_body selected actual_body (by intro bad;cases bad) parameters bodyEvery (by intro label;rfl) (convert64 _ carry64)
    simp only [after,paramScope]
  have wo:=wellScoped_declare we dOut
  have wa:=wellScoped_declare wo da
  have wn:=wellScoped_declare wa dn
  have wi:=wellScoped_declare wn di
  have f1:=ApplicationBirthFrame.declare_frame entry.nextObject [input.layout.outObject] we (le_refl _) dOut
  have f2:=ApplicationBirthFrame.declare_frame entry.nextObject [input.layout.outObject] wo f1.fresh da
  have f3:=ApplicationBirthFrame.declare_frame entry.nextObject [input.layout.outObject] wa f2.fresh dn
  have f4:=ApplicationBirthFrame.declare_frame entry.nextObject [input.layout.outObject] wn f3.fresh di
  have f5:=ApplicationBirthFrame.declare_frame entry.nextObject [input.layout.outObject] wi f4.fresh dc
  have prefixFrame:=f1.trans (f2.trans (f3.trans (f4.trans f5)))
  have whole:=prefixFrame.trans loopFrame
  have enteredFrame : ApplicationBirthFrame.Frame before.nextObject before.enterScope finished [input.layout.outObject]:=
    ⟨whole.well,whole.fresh,whole.nextObject,whole.nextScope,whole.mode,whole.foreign,whole.outside⟩
  have frame:=ApplicationBirthFrame.close_frame well (le_refl _) enteredFrame
  exact ⟨after,called,everyCalled,IncrementSource.wordArray_leave post.array,full_caller_frame rfl rfl frame⟩

#print axioms add_magnitude_call
end RH080Next.FFTPV.AddMagnitudeSource
