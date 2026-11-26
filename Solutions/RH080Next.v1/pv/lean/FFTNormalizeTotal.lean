/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTNormalizeProfiles
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.NormalizeSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings

theorem caller_frame_trans {F : Type} {a b c : State F} {workObject : Nat}
    (first : MultiplyCall.CallerFrame a b [workObject]) (second : MultiplyCall.CallerFrame b c [workObject]) :
    MultiplyCall.CallerFrame a c [workObject] := by
  refine ⟨second.environment.trans first.environment,second.scope.trans first.scope,
    second.frame.well,first.frame.nextObject.trans second.frame.fresh,first.frame.nextObject.trans second.frame.nextObject,
    first.frame.nextScope.trans second.frame.nextScope,second.frame.mode.trans first.frame.mode,
    second.frame.foreign.trans first.frame.foreign,?_⟩
  intro id old away
  exact (second.frame.outside id (lt_of_lt_of_le old first.frame.nextObject) away).trans (first.frame.outside id old away)

def totalStatements (fap : Bool) : List Stmt:=if fap then [divideStmt false nDivisor]
  else [divideStmt false (literal 100),divideStmt false nDivisor]
def totalData (fap : Bool) (old : Nat→Nat) (n : Nat) : Nat→Nat:=
  if fap then DivideSource.roundedData old 192 6 n 1
  else DivideSource.roundedData (DivideSource.roundedData old 192 6 100 1) 192 6 n 1

def totalValue (fap : Bool) (oldMagnitude n : Nat) : Nat:=
  if fap then FFT.Limbs.ceilQuotient oldMagnitude n
  else FFT.Limbs.ceilQuotient (FFT.Limbs.ceilQuotient oldMagnitude 100) n

/-- Concrete original Fap/W4 total normalization, including every actual Call
and the exact original ordering of the upward divisions. -/
theorem total_execution {F : Type} (context : Context F)
    (selected : findFunction context.program "divide_small"=some divide_small_ast)
    (increment : findFunction context.program "increment_words"=some increment_words_ast)
    (fap : Bool) {before : State F} {workObject n owner : Nat} {ids : Var→Nat} {old : Nat→Nat}
    (params : Locals before name type ids owner (values workObject n))
    (array : WordArrayRep before workObject 512 old) (separate : ∀v,workObject≠ids v) (well : WellScoped before)
    (positive : 0<n) (small : n<1000000000) (digits : ∀k,k<6 → old (192+k)<1000000000) :
    ∃after dataAfter,ExecList context before (totalStatements fap) .normal after ∧
      WordArrayRep after workObject 512 dataAfter ∧
      Locals after name type ids owner (values workObject n) ∧
      MultiplyCall.CallerFrame before after [workObject] ∧
      FFT.Limbs.magnitude 1000000000 6 (fun k=>dataAfter (192+k))=
        totalValue fap (FFT.Limbs.magnitude 1000000000 6 (fun k=>old (192+k))) n ∧
      (∀k,k<6 → dataAfter (192+k)<1000000000) ∧
      (∀k,(k<192 ∨ 198≤k) → dataAfter k=old k) ∧
      (∀other flow,ExecList context before (totalStatements fap) flow other → flow=.normal ∧ other=after) := by
  cases fap with
  | true=>
    obtain ⟨after,run,rep,locs,frame,value,normalized,outside,every⟩:=
      division_execution context selected increment (old:=old) params array separate well false nDivisor n positive small (by trivial) (n_eval context params) digits
    refine ⟨after,DivideSource.roundedData old (start false) 6 n 1,.cons run .nil,rep,locs,frame,value,normalized,outside,?_⟩
    intro other flow arbitrary
    cases arbitrary with
    | abrupt actual abnormal=>exact False.elim (abnormal (every _ _ actual).1)
    | cons actual tail=>
      obtain ⟨_,eqs⟩:=every _ _ actual
      cases eqs
      cases tail
      exact ⟨rfl,rfl⟩
  | false=>
    obtain ⟨middle,first,midRep,midParams,firstFrame,firstValue,midDigits,midOutside,firstEvery⟩:=
      division_execution context selected increment (old:=old) params array separate well false (literal 100) 100 (by norm_num) (by norm_num)
        (by trivial) (literal_eval context before 100 (by norm_num)) digits
    obtain ⟨after,second,rep,locs,secondFrame,secondValue,normalized,outside,secondEvery⟩:=
      division_execution context selected increment (old:=DivideSource.roundedData old 192 6 100 1) midParams midRep separate firstFrame.frame.well false nDivisor n positive small
        (by trivial) (n_eval context midParams) midDigits
    have value:=secondValue.trans (congrArg (fun m=>FFT.Limbs.ceilQuotient m n) firstValue)
    refine ⟨after,DivideSource.roundedData (DivideSource.roundedData old (start false) 6 100 1) (start false) 6 n 1,.cons first (.cons second .nil),rep,locs,caller_frame_trans firstFrame secondFrame,value,normalized,?_,?_⟩
    · intro k away
      exact (outside k away).trans (midOutside k away)
    · intro other flow arbitrary
      cases arbitrary with
      | abrupt actual abnormal=>exact False.elim (abnormal (firstEvery _ _ actual).1)
      | cons actual tail=>
        obtain ⟨_,eqs⟩:=firstEvery _ _ actual
        cases eqs
        cases tail with
        | abrupt actual abnormal=>exact False.elim (abnormal (secondEvery _ _ actual).1)
        | cons actual tail=>
          obtain ⟨_,eqs⟩:=secondEvery _ _ actual
          cases eqs
          cases tail
          exact ⟨rfl,rfl⟩

#print axioms total_execution
end RH080Next.FFTPV.NormalizeSource
