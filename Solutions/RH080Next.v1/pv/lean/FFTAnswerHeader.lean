/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTAnswerConvertDeclaration
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.AnswerSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings
open ApplicationBirthFrame

inductive MainVar where | total | quad | status | answer deriving DecidableEq

def lift : MainVar→Var | .total=>.total | .quad=>.quad | .status=>.status | .answer=>.answer

def combinedIds (ids : MainVar→Nat) (firstId secondId : Nat) : Var→Nat
  | .total=>ids .total | .quad=>ids .quad | .status=>ids .status | .answer=>ids .answer | .first=>firstId | .second=>secondId

def combinedOwners (parent child : Nat) : Var→Nat | .first | .second=>child | _=>parent

def firstValue (data : Nat→Nat) : Nat:=ConvertBoundSource.result data 192
def secondValue (data : Nat→Nat) : Nat:=ConvertBoundSource.result data 208

private theorem locals_after_birth {F I : Type} {before after : State F}
    {names : I→String} {types : I→CType} {ids : I→Nat} {owner : Nat} {vals : I→Value}
    {declarationName : String} {newId : Nat}
    (params : Locals before names types ids owner vals) (well : WellScoped before)
    (frame : Frame before.nextObject before after [])
    (environment : after.environment=(declarationName,scalarPointer newId .u64)::before.environment)
    (different : ∀v,names v≠declarationName) : Locals after names types ids owner vals:=by
  refine ⟨?_,?_,params.distinct,params.bound.trans_le frame.nextScope⟩
  · intro v
    rw [environment]
    simpa [List.lookup,show (names v == declarationName)=false from beq_false_of_ne (different v)] using params.lookup v
  · intro v
    exact ⟨(params.slots v).storable,(frame.outside (ids v) (well.objectIds _ _ (params.slots v).object) (by simp)).trans (params.slots v).object⟩

private theorem frame_trans_fresh {F : Type} {a b c : State F}
    (first : Frame a.nextObject a b []) (second : Frame b.nextObject b c []) : Frame a.nextObject a c [] := by
  refine ⟨second.well,first.nextObject.trans second.fresh,first.nextObject.trans second.nextObject,
    first.nextScope.trans second.nextScope,second.mode.trans first.mode,second.foreign.trans first.foreign,?_⟩
  intro id old away
  exact (second.outside id (lt_of_lt_of_le old first.nextObject) away).trans (first.outside id old away)

/-- Real converted first/second values and their actual automatic objects are
constructed in the active if-block scope; parent bindings retain their own
older owners. Both conversion calls preserve every old application object. -/
theorem header_execution {F : Type} (context : Context F)
    (selected : findFunction context.program "convert_bound"=some convert_bound_ast)
    (before : State F) (workObject owner prior : Nat) (ids : MainVar→Nat) (data : Nat→Nat)
    (params : Locals before (fun v=>name (lift v)) (fun v=>type (lift v)) ids owner
      (fun v=>values workObject 0 0 prior (lift v)))
    (array : WordArrayRep before workObject 512 data) (separate : ∀v,workObject≠ids v) (well : WellScoped before)
    (priorFits : prior<2^64) (totalDigits : ∀k,k<6 → data (192+k)<1000000000)
    (quadDigits : ∀k,k<6 → data (208+k)<1000000000) :
    ∃after firstId secondId,ExecList context before [firstDeclaration,secondDeclaration] .normal after ∧
      View after workObject (combinedIds ids firstId secondId) (combinedOwners owner before.scope)
        (firstValue data) (secondValue data) prior data ∧
      Frame before.nextObject before after [] ∧ after.scope=before.scope ∧
      (∀other flow,ExecList context before [firstDeclaration,secondDeclaration] flow other → flow=.normal ∧ other=after) := by
  obtain ⟨middle,firstId,firstRun,firstSlot,firstEnv,firstScope,firstFresh,firstArray,firstFrame,firstEvery⟩:=
    convert_declaration context selected before workObject 192 (ids MainVar.total) owner data "total" "first"
      (params.lookup MainVar.total) (params.slots MainVar.total) array (by norm_num) totalDigits well
  have middleParams:=locals_after_birth params well firstFrame firstEnv (by intro v;cases v <;> decide)
  obtain ⟨after,secondId,secondRun,secondSlot,secondEnv,secondScope,secondFresh,secondArray,secondFrame,secondEvery⟩:=
    convert_declaration context selected middle workObject 208 (ids MainVar.quad) owner data "quad" "second"
      (middleParams.lookup MainVar.quad) (middleParams.slots MainVar.quad) firstArray (by norm_num) quadDigits firstFrame.well
  have finalParams:=locals_after_birth middleParams firstFrame.well secondFrame secondEnv (by intro v;cases v <;> decide)
  have firstBound : firstId<middle.nextObject:=firstFrame.well.objectIds _ _ firstSlot.object
  have firstAfter : Slot after firstId before.scope .u64 (.integer (integer64 (firstValue data))):=
    ⟨firstSlot.storable,(secondFrame.outside firstId firstBound (by simp)).trans firstSlot.object⟩
  have secondAfter : Slot after secondId before.scope .u64 (.integer (integer64 (secondValue data))):=by
    simpa only [firstScope,secondValue] using secondSlot
  have allFrame:=frame_trans_fresh firstFrame secondFrame
  have combined : ProductInner.Bindings after name type (combinedIds ids firstId secondId)
      (combinedOwners owner before.scope) (values workObject (firstValue data) (secondValue data) prior) := by
    constructor
    · intro v
      cases v with
      | total=>exact finalParams.lookup MainVar.total
      | quad=>exact finalParams.lookup MainVar.quad
      | status=>exact finalParams.lookup MainVar.status
      | answer=>exact finalParams.lookup MainVar.answer
      | first=>simp [combinedIds,name,type,secondEnv,firstEnv,scalarPointer,List.lookup]
      | second=>simp [combinedIds,name,type,secondEnv,scalarPointer,List.lookup]
    · intro v
      cases v with
      | total=>exact finalParams.slots MainVar.total
      | quad=>exact finalParams.slots MainVar.quad
      | status=>exact finalParams.slots MainVar.status
      | answer=>exact finalParams.slots MainVar.answer
      | first=>exact firstAfter
      | second=>exact secondAfter
    · intro v w equal
      have oldBounds : ∀v,ids v<before.nextObject:=fun v=>well.objectIds _ _ (params.slots v).object
      have bt:=oldBounds MainVar.total
      have bq:=oldBounds MainVar.quad
      have bs:=oldBounds MainVar.status
      have ba:=oldBounds MainVar.answer
      have distinct : ∀v w : MainVar,v≠w → ids v≠ids w:=fun v w ne eq=>ne (params.distinct eq)
      cases v <;> cases w <;> simp only [combinedIds] at equal ⊢
      all_goals first | rfl | exact False.elim (distinct _ _ (by decide) equal) | omega
    · intro v
      cases v <;> simp only [combinedOwners]
      all_goals first
        | exact finalParams.bound
        | (have scope:=secondScope.trans firstScope;rw [←scope];exact allFrame.well.current)
  have oldWork : workObject<before.nextObject:=well.objectIds _ _ array.2.1
  have view : View after workObject (combinedIds ids firstId secondId) (combinedOwners owner before.scope)
      (firstValue data) (secondValue data) prior data := by
    refine ⟨combined,secondArray,?_,ConvertBoundSource.result_fits data 192 totalDigits,
      ConvertBoundSource.result_fits data 208 quadDigits,priorFits,allFrame.well⟩
    intro v
    cases v <;> simp only [combinedIds] <;> first | exact separate _ | omega
  refine ⟨after,firstId,secondId,.cons firstRun (.cons secondRun .nil),view,allFrame,secondScope.trans firstScope,?_⟩
  intro other flow run
  cases run with
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

#print axioms header_execution
end RH080Next.FFTPV.AnswerSource
