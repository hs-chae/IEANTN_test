/- Generic semantic facts used to add a precise stdio boundary to the
preserved source program. No application output occurs in these facts. -/
import FFTSourceOutput
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.MainIO
open GoldbachDirect GoldbachDirect.Semantics GoldbachDirect.SourceLocals

theorem bindParameters_foreign {F : Type} {before after : State F}
    {parameters : List (CType × String)} {values : List Value}
    (bound : bindParameters before parameters values = some after) :
    after.foreign=before.foreign := by
  induction parameters generalizing before values with
  | nil => cases values <;> simp_all [bindParameters]
  | cons parameter parameters ih =>
    rcases parameter with ⟨type,name⟩
    cases values with
    | nil => simp [bindParameters] at bound
    | cons value values =>
      cases declared : before.declare type name (some value) with
      | none => simp [bindParameters,declared] at bound
      | some middle =>
        have tail : bindParameters middle parameters values=some after := by
          simpa [bindParameters,declared] using bound
        exact (ih tail).trans (declare_foreign declared)

/-- A context whose individual foreign operations preserve the extra state
also preserves that state through arbitrary source execution. -/
theorem call_foreign_frame {F : Type} {context : Context F}
    (foreignFrame : ∀primitive values before result after,
      context.foreign primitive values before result after → after.foreign=before.foreign)
    {name : String} {values : List Value} {before after : State F} {result : CallResult}
    (run : Call context name values before result after) : after.foreign=before.foreign := by
  apply Call.rec
    (motive_1:=fun before _ _ after _=>after.foreign=before.foreign)
    (motive_2:=fun before _ _ after _=>after.foreign=before.foreign)
    (motive_3:=fun before _ _ after _=>after.foreign=before.foreign)
    (motive_4:=fun before _ _ after _=>after.foreign=before.foreign)
    (motive_5:=fun before _ _ after _=>after.foreign=before.foreign)
    (motive_6:=fun before _ _ after _=>after.foreign=before.foreign)
    (motive_7:=fun _ before _ _ after _=>after.foreign=before.foreign)
    (motive_8:=fun _ _ before _ after _=>after.foreign=before.foreign)
    (t:=run)
  case internal =>
    intro name function statements values entered value middle result after before selected shape parameters body converted finished ih
    have boundFrame := bindParameters_foreign parameters
    simpa only [finished,State.leaveScope,State.enterScope] using ih.trans boundFrame
  case internalVoid =>
    intro name function statements values entered middle after before selected shape void parameters body finished ih
    have boundFrame := bindParameters_foreign parameters
    simpa only [finished,State.leaveScope,State.enterScope] using ih.trans boundFrame
  case internalTerminated =>
    intro name function statements values entered status after before selected shape parameters body ih
    have boundFrame := bindParameters_foreign parameters
    simpa only [State.enterScope] using ih.trans boundFrame
  all_goals intros
  all_goals first
    | rfl
    | assumption
    | grind only [State.enterScope,State.leaveScope,store_foreign,declare_foreign]

/-- Extending only the generic foreign relation admits every previously
constructed execution, including all possible source argument orders. -/
theorem call_extend_foreign {F : Type} {context : Context F} (foreign : Foreign F)
    (inclusion : ∀primitive values before result after,
      context.foreign primitive values before result after → foreign primitive values before result after)
    {name : String} {values : List Value} {before after : State F} {result : CallResult}
    (run : Call context name values before result after) :
    Call {context with foreign:=foreign} name values before result after := by
  apply Call.rec
    (motive_1:=fun before expression value after _=>Eval {context with foreign:=foreign} before expression value after)
    (motive_2:=fun before expression value after _=>Place {context with foreign:=foreign} before expression value after)
    (motive_3:=fun before expressions values after _=>ArgSequence {context with foreign:=foreign} before expressions values after)
    (motive_4:=fun before expressions values after _=>Args {context with foreign:=foreign} before expressions values after)
    (motive_5:=fun before statement flow after _=>Exec {context with foreign:=foreign} before statement flow after)
    (motive_6:=fun before statements flow after _=>ExecList {context with foreign:=foreign} before statements flow after)
    (motive_7:=fun whole before statements flow after _=>Body {context with foreign:=foreign} whole before statements flow after)
    (motive_8:=fun name values before result after _=>Call {context with foreign:=foreign} name values before result after)
    (t:=run)
  all_goals intros
  all_goals first
    | (apply Eval.literal <;> assumption)
    | (apply Eval.paren <;> assumption)
    | (apply Eval.variable <;> assumption)
    | (apply Eval.constant <;> assumption)
    | (apply Eval.builtin <;> assumption)
    | (apply Eval.address <;> assumption)
    | (apply Eval.load <;> assumption)
    | (apply Eval.cast <;> assumption)
    | (apply Eval.unary <;> assumption)
    | (apply Eval.binaryLR <;> assumption)
    | (apply Eval.binaryRL <;> assumption)
    | (apply Eval.andFalse <;> assumption)
    | (apply Eval.andTrue <;> assumption)
    | (apply Eval.orTrue <;> assumption)
    | (apply Eval.orFalse <;> assumption)
    | (apply Eval.conditionalTrue <;> assumption)
    | (apply Eval.conditionalFalse <;> assumption)
    | (apply Eval.call <;> assumption)
    | (apply Place.variable <;> assumption)
    | (apply Place.paren <;> assumption)
    | (apply Place.dereference <;> assumption)
    | (apply Place.index <;> assumption)
    | (apply ArgSequence.nil)
    | (apply ArgSequence.cons <;> assumption)
    | (apply Args.ordered <;> assumption)
    | (apply Exec.block <;> assumption)
    | (apply Exec.declareNone <;> assumption)
    | (apply Exec.declareSome <;> assumption)
    | (apply Exec.assign <;> assumption)
    | (apply Exec.assignOp <;> assumption)
    | (apply Exec.expression <;> assumption)
    | (apply Exec.callTerminated <;> assumption)
    | (apply Exec.ifTrue <;> assumption)
    | (apply Exec.ifFalse <;> assumption)
    | (apply Exec.ifElse <;> assumption)
    | (apply Exec.whileFalse <;> assumption)
    | (apply Exec.whileNext <;> assumption)
    | (apply Exec.whileContinue <;> assumption)
    | (apply Exec.whileBreak <;> assumption)
    | (apply Exec.whileExit <;> assumption)
    | (apply Exec.returnNone)
    | (apply Exec.returnSome <;> assumption)
    | (apply Exec.breakLoop)
    | (apply Exec.continueLoop)
    | (apply Exec.label)
    | (apply Exec.gotoLabel)
    | (apply Exec.launch <;> first | assumption | exact inclusion _ _ _ _ _ (by assumption))
    | (apply ExecList.nil)
    | (apply ExecList.cons <;> assumption)
    | (apply ExecList.abrupt <;> assumption)
    | (apply Body.finish <;> assumption)
    | (apply Body.jump <;> assumption)
    | (apply Call.external <;> first | assumption | exact inclusion _ _ _ _ _ (by assumption))
    | (apply Call.internal <;> assumption)
    | (apply Call.internalVoid <;> assumption)
    | (apply Call.internalTerminated <;> assumption)

end RH080Next.FFTPV.MainIO
