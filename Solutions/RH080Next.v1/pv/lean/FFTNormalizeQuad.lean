/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTNormalizeTotal
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.NormalizeSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings

def quadStatements : List Stmt:=[divideStmt true (literal 3),divideStmt true nDivisor,divideStmt true nDivisor]
def quadData (old : Nat→Nat) (n : Nat) : Nat→Nat:=DivideSource.roundedData
  (DivideSource.roundedData (DivideSource.roundedData old 208 6 3 1) 208 6 n 1) 208 6 n 1

def quadValue (oldMagnitude n : Nat) : Nat:=FFT.Limbs.ceilQuotient
  (FFT.Limbs.ceilQuotient (FFT.Limbs.ceilQuotient oldMagnitude 3) n) n

/-- All three original source calls for the chord-error accumulator, with exact
successive upward quotients and preservation of the separate total slice. -/
theorem quad_execution {F : Type} (context : Context F)
    (selected : findFunction context.program "divide_small"=some divide_small_ast)
    (increment : findFunction context.program "increment_words"=some increment_words_ast)
    {before : State F} {workObject n owner : Nat} {ids : Var→Nat} {old : Nat→Nat}
    (params : Locals before name type ids owner (values workObject n))
    (array : WordArrayRep before workObject 512 old) (separate : ∀v,workObject≠ids v) (well : WellScoped before)
    (positive : 0<n) (small : n<1000000000) (digits : ∀k,k<6 → old (208+k)<1000000000) :
    ∃after dataAfter,ExecList context before quadStatements .normal after ∧
      WordArrayRep after workObject 512 dataAfter ∧
      Locals after name type ids owner (values workObject n) ∧
      MultiplyCall.CallerFrame before after [workObject] ∧
      FFT.Limbs.magnitude 1000000000 6 (fun k=>dataAfter (208+k))=
        quadValue (FFT.Limbs.magnitude 1000000000 6 (fun k=>old (208+k))) n ∧
      (∀k,k<6 → dataAfter (208+k)<1000000000) ∧
      (∀k,(k<208 ∨ 214≤k) → dataAfter k=old k) ∧
      (∀other flow,ExecList context before quadStatements flow other → flow=.normal ∧ other=after) := by
  obtain ⟨s1,first,rep1,params1,frame1,value1,digits1,outside1,every1⟩:=
    division_execution context selected increment (old:=old) params array separate well true (literal 3) 3 (by norm_num) (by norm_num)
      (by trivial) (literal_eval context before 3 (by norm_num)) digits
  obtain ⟨s2,second,rep2,params2,frame2,value2,digits2,outside2,every2⟩:=
    division_execution context selected increment (old:=DivideSource.roundedData old 208 6 3 1) params1 rep1 separate frame1.frame.well true nDivisor n positive small
      (by trivial) (n_eval context params1) digits1
  obtain ⟨after,third,rep,locs,frame3,value3,normalized,outside3,every3⟩:=
    division_execution context selected increment (old:=DivideSource.roundedData (DivideSource.roundedData old 208 6 3 1) 208 6 n 1) params2 rep2 separate frame2.frame.well true nDivisor n positive small
      (by trivial) (n_eval context params2) digits2
  have secondValue:=value2.trans (congrArg (fun m=>FFT.Limbs.ceilQuotient m n) value1)
  have value:=value3.trans (congrArg (fun m=>FFT.Limbs.ceilQuotient m n) secondValue)
  refine ⟨after,DivideSource.roundedData (DivideSource.roundedData (DivideSource.roundedData old (start true) 6 3 1) (start true) 6 n 1) (start true) 6 n 1,.cons first (.cons second (.cons third .nil)),rep,locs,caller_frame_trans frame1 (caller_frame_trans frame2 frame3),value,normalized,?_,?_⟩
  · intro k away
    exact (outside3 k away).trans ((outside2 k away).trans (outside1 k away))
  · intro other flow arbitrary
    cases arbitrary with
    | abrupt actual abnormal=>exact False.elim (abnormal (every1 _ _ actual).1)
    | cons actual tail=>
      obtain ⟨_,eqs⟩:=every1 _ _ actual
      cases eqs
      cases tail with
      | abrupt actual abnormal=>exact False.elim (abnormal (every2 _ _ actual).1)
      | cons actual tail=>
        obtain ⟨_,eqs⟩:=every2 _ _ actual
        cases eqs
        cases tail with
        | abrupt actual abnormal=>exact False.elim (abnormal (every3 _ _ actual).1)
        | cons actual tail=>
          obtain ⟨_,eqs⟩:=every3 _ _ actual
          cases eqs
          cases tail
          exact ⟨rfl,rfl⟩

#print axioms quad_execution
end RH080Next.FFTPV.NormalizeSource
