/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTRootSetupFramed
import ExplicitFFTRootTail
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.RootSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings

def startStatements : List Stmt:=xPrefixStatements++squareStatement::setupStatements++[indexDeclaration]

theorem source_list_split : sourceStatements=startStatements++sourceLoop::tailStatements:=by rfl

/-- Actual complete application prefix, including all runtime-dependent births
and initialization. The exact physical memory outside work80 and root12 is
preserved, rather than assumed from a whole-object frame. -/
theorem start_execution {F : Type} (context : Context F) (functions : Functions context)
    {before : State F} {input : Input} {owner : Nat} {ids : Param → Nat}
    (h : ParamView before input owner ids input.old) (scope : before.scope=owner) (grid : OriginalGrid input.n) :
    ∃after nextData statusId indexId,ExecList context before startStatements .normal after ∧
      EveryList context before startStatements .normal after ∧
      Runtime after input owner statusId indexId ids nextData 1 ∧ Tracked input nextData (regionValue input.n 0) ∧
      ApplicationBirthFrame.Frame before.nextObject before after [input.layout.object] ∧ after.scope=owner ∧
      ∀k,k< input.layout.size → (k< input.layout.workStart ∨ input.layout.workStart+80≤ k) →
        (k< input.layout.rootStart ∨ input.layout.rootStart+12≤ k) → nextData k=input.old k := by
  have workBound:=input.layout.workBound
  obtain ⟨piState,piRun,piEvery,piView,piFrame⟩:=pi_prefix_framed context functions.zero h scope
  obtain ⟨returned,scaled,scaleRun,scaleEvery,declared,scaleView,scaleScope,scaleFrame⟩:=scale_framed context functions.multiplySmall piView (piFrame.scope.trans scope)
  obtain ⟨divided,divideRun,divideEvery,divideView,divideScope,divideFrame⟩:=divide_framed context functions.divide functions.increment scaleView scaleScope
  have x : FixedValue (xData input) (pointerStart input .work+0) (xInteger input.n):=xData_fixed input
  have xSmall : (xInteger input.n).natAbs≤1000*10^36:=by rcases grid with hn|hn <;> rw [hn] <;> decide
  obtain ⟨squared,dataSquare,squareRun,squareEvery,squareView,squareValue,squareFrame,squareOutside⟩:=multiply_execution context functions.multiply functions.zero functions.increment functions.canonical
    divideView divideScope.ge .work (Or.inr rfl) 6 .work (Or.inr rfl) 0 .work (Or.inr rfl) 0
    (xInteger input.n) (xInteger input.n) x x xSmall xSmall
    (by simp only [pointerStart];omega) (by simp only [pointerStart];omega) (by simp only [pointerStart];omega)
    (Or.inl (by simp only [pointerStart];omega)) (Or.inl (by simp only [pointerStart];omega))
    (Or.inl (by simp only [pointerStart];omega)) (by norm_num) (by norm_num) (by norm_num)
  have squareScope : squared.scope=owner:=squareFrame.scope.trans divideScope
  have xKept : FixedValue dataSquare input.layout.workStart (xInteger input.n):=by
    apply (xData_fixed input).congr
    intro k hk
    exact squareOutside _ (by omega) (Or.inl (by simp only [pointerStart];omega)) (Or.inl (by omega))
  have x2 : FixedValue dataSquare (input.layout.workStart+6) (x2Integer input.n):=squareValue
  have zeroCt : ∀k < 6,dataSquare (input.layout.workStart+12+k)=0:=by
    intro k hk
    rw [squareOutside _ (by omega) (Or.inr (by simp only [pointerStart];omega)) (Or.inl (by omega))]
    simpa only [Nat.add_assoc] using xData_zero_work input (12+k) (by omega) (by omega)
  obtain ⟨setup,setupRun,setupEvery,setupView,setupFrame⟩:=setup_framed context functions.zero functions.copy squareView squareScope
  have values:=setup_values input dataSquare xKept x2 zeroCt
  have setupScope : setup.scope=owner:=setupFrame.scope.trans squareScope
  obtain ⟨after,indexRun,indexEvery,runtime,afterScope⟩:=index_declaration_execution context setupView setupScope
  have indexFrame:=declaration_birth_frame (object:=input.layout.object) setupView.params.well (by trivial)
    (.literal (.integer 1 "ULL") _ (.integer (integer64 1)) (by rfl)) indexRun
  have frame0:=unary_frame piFrame
  have frame1:=frame0.trans (lower_frame scaleFrame frame0.nextObject)
  have frame2:=frame1.trans (lower_frame (unary_frame divideFrame) frame1.nextObject)
  have frame3:=frame2.trans (lower_frame (multiply_frame squareFrame) frame2.nextObject)
  have frame4:=frame3.trans (lower_frame (unary_frame setupFrame) frame3.nextObject)
  have frame5:=frame4.trans (lower_frame indexFrame.1 frame4.nextObject)
  refine ⟨after,setupData input dataSquare,returned.nextObject,setup.nextObject,?_,?_,runtime,values.tracked,frame5,afterScope,?_⟩
  · have setupEnding : ExecList context squared (setupStatements++[indexDeclaration]) .normal after:=
      append_normal (xs:=setupStatements) (ys:=[indexDeclaration]) setupRun (.cons indexRun .nil)
    have ending : ExecList context piState ([scaleStatement,divideStatement,squareStatement]++(setupStatements++[indexDeclaration])) .normal after:=
      .cons scaleRun (.cons divideRun (.cons squareRun setupEnding))
    change ExecList context before (prefixStatements++([scaleStatement,divideStatement,squareStatement]++(setupStatements++[indexDeclaration]))) .normal after
    exact append_normal (xs:=prefixStatements) (ys:=[scaleStatement,divideStatement,squareStatement]++(setupStatements++[indexDeclaration])) piRun ending
  · have setupEnding : EveryList context squared (setupStatements++[indexDeclaration]) .normal after:=
      every_append (xs:=setupStatements) (ys:=[indexDeclaration]) setupEvery (every_cons indexEvery (every_nil after))
    have ending : EveryList context piState ([scaleStatement,divideStatement,squareStatement]++(setupStatements++[indexDeclaration])) .normal after:=
      every_cons scaleEvery (every_cons divideEvery (every_cons squareEvery setupEnding))
    change EveryList context before (prefixStatements++([scaleStatement,divideStatement,squareStatement]++(setupStatements++[indexDeclaration]))) .normal after
    exact every_append (xs:=prefixStatements) (ys:=[scaleStatement,divideStatement,squareStatement]++(setupStatements++[indexDeclaration])) piEvery ending
  · intro k hk outsideWork outsideRoot
    rw [setupData_outside input dataSquare k outsideWork outsideRoot]
    rw [squareOutside k hk (by simp only [pointerStart];rcases outsideWork with lo|hi <;> omega)
      (by rcases outsideWork with lo|hi <;> omega)]
    exact xData_outside_work input k outsideWork

#print axioms source_list_split
#print axioms start_execution
end RH080Next.FFTPV.RootSource
