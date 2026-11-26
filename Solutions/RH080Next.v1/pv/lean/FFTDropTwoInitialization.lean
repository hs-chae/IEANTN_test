/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTDropTwoRoundSource
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.DropTwoSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings
open ApplicationBirthFrame

inductive InitVar where | total | i | status deriving DecidableEq

def lift : InitVar→Var | .total=>.total | .i=>.i | .status=>.status

def combinedIds (ids : InitVar→Nat) (newId : Nat) : Var→Nat
  | .total=>ids .total | .i=>ids .i | .status=>ids .status | .lost=>newId

def lostDeclaration : Stmt:=.declare .u64 "lost" (some (.paren (.binary .add
  (.index (.variable "total") (.literal (.integer 0 "ULL"))) (.index (.variable "total") (.literal (.integer 1 "ULL"))))))
def iReset : Stmt:=.assign (.variable "i") (.literal (.integer 0 "ULL"))

theorem actual_lost_declaration : (ProductRow.items FFTRecursivePV.w4_recursive_norm_upper_ast.body)[26]?=some lostDeclaration:=by rfl
theorem actual_i_reset : (ProductRow.items FFTRecursivePV.w4_recursive_norm_upper_ast.body)[27]?=some iReset:=by rfl

theorem initialize_drop {F : Type} (context : Context F) (before : State F) (workObject previous : Nat)
    (ids : InitVar→Nat) (old : Nat→Nat) (well : WellScoped before)
    (params : Locals before (fun v=>name (lift v)) (fun v=>type (lift v)) ids before.scope
      (fun v=>values workObject old previous (lift v)))
    (array : WordArrayRep before workObject 512 old) (digits : ∀k,k<6 → old (192+k)<base) :
    ∃after newId,ExecList context before [lostDeclaration,iReset] .normal after ∧
      View after workObject (combinedIds ids newId) before.scope 0 old ∧
      Frame before.nextObject before after [ids InitVar.i] ∧ before.nextObject≤newId := by
  have separate : ∀v,workObject≠ids v:=fun v=>MultiplyParameters.array_slot_different array (params.slots v)
  have h0:=digits 0 (by norm_num)
  have h1:=digits 1 (by norm_num)
  have fits : lost old 192<2^64:=by dsimp [lost,base] at *;omega
  have index0 : Eval context before (.index (.variable "total") (.literal (.integer 0 "ULL"))) (.integer (integer64 (old 192))) before:=by
    exact .load (.index (.variable (params.lookup InitVar.total) (params.read InitVar.total))
      (.literal (.integer 0 "ULL") _ (.integer (integer64 0)) (by rfl)) (by simpa using slice_pointer_add array (start:=192) (i:=0) (by norm_num)))
      (by simpa using word_load array (show 192+0<512 by norm_num))
  have index1 : Eval context before (.index (.variable "total") (.literal (.integer 1 "ULL"))) (.integer (integer64 (old 193))) before:=by
    exact .load (.index (.variable (params.lookup InitVar.total) (params.read InitVar.total))
      (.literal (.integer 1 "ULL") _ (.integer (integer64 1)) (by rfl)) (slice_pointer_add array (start:=192) (i:=1) (by norm_num)))
      (word_load array (show 192+1<512 by norm_num))
  have computed : Eval context before (.paren (.binary .add (.index (.variable "total") (.literal (.integer 0 "ULL")))
      (.index (.variable "total") (.literal (.integer 1 "ULL"))))) (.integer (integer64 (lost old 192))) before:=
    .paren (.binaryLR index0 index1 (by
      have add:=binary64_add (old 192) (old 193) (by dsimp [base] at h0;omega) (by dsimp [base] at h1;omega) fits
      simp only [binary,lost,add,Option.map_some]))
  obtain ⟨middle,declared⟩:=ZeroFrame.declare_exists well .u64 "lost" (.integer (integer64 (lost old 192))) (ZeroFrame.u64_storable _ fits)
  have birth:=declare_storable (ZeroFrame.u64_storable _ fits) (convert64 _ fits) declared
  have wm:=wellScoped_declare well declared
  have oldParams:=ApplicationBirthFrame.locals_declare_old well params (by intro v;cases v <;> decide) birth
  have workOld:=well.objectIds _ _ array.2.1
  have newParams : Locals middle name type (combinedIds ids before.nextObject) before.scope (values workObject old previous):=by
    constructor
    · intro v;cases v with
      | total=>exact oldParams.lookup InitVar.total
      | i=>exact oldParams.lookup InitVar.i
      | status=>exact oldParams.lookup InitVar.status
      | lost=>simp [combinedIds,name,type,scalarPointer,birth.environment]
    · intro v;cases v with
      | total=>exact oldParams.slots InitVar.total
      | i=>exact oldParams.slots InitVar.i
      | status=>exact oldParams.slots InitVar.status
      | lost=>exact birth.slot
    · intro v w equal
      have hn:=well.objectIds _ _ (params.slots InitVar.total).object
      have hi:=well.objectIds _ _ (params.slots InitVar.i).object
      have hs:=well.objectIds _ _ (params.slots InitVar.status).object
      have different : ∀v w : InitVar,v≠w → ids v≠ids w:=fun v w ne eq=>ne (params.distinct eq)
      cases v <;> cases w <;> simp only [combinedIds] at equal ⊢
      all_goals first | rfl | exact False.elim (different _ _ (by decide) equal) | omega
    · rw [birth.nextScope];exact params.bound
  have ar : WordArrayRep middle workObject 512 old:=
    ⟨birth.mode.trans array.1,(birth.outside workObject (by omega)).trans array.2.1,array.2.2⟩
  obtain ⟨after,written⟩:=ProductInner.slot_store_exists (newParams.slots Var.i) (.integer (integer64 0)) (ZeroFrame.u64_storable 0 (by norm_num))
  have reset : Exec context middle iReset .normal after:=.assign (.literal (.integer 0 "ULL") _ _ (by rfl)) (.variable (newParams.lookup Var.i)) written
  have finalParams:=newParams.store Var.i (.integer (integer64 0)) (ZeroFrame.u64_storable 0 (by norm_num)) written
  have eq : Function.update (values workObject old previous) Var.i (.integer (integer64 0))=values workObject old 0:=by
    funext v;cases v <;> simp [values,Function.update]
  rw [eq] at finalParams
  have fields:=SourceLocals.store_frame written
  have finalArray : WordArrayRep after workObject 512 old:=
    ⟨fields.2.1.trans ar.1,(fields.2.2.2.2.2 workObject (separate InitVar.i)).trans ar.2.1,ar.2.2⟩
  have post : View after workObject (combinedIds ids before.nextObject) before.scope 0 old:=by
    refine ⟨finalParams,finalArray,?_,digits,by norm_num,wellScoped_store wm written⟩
    intro v;cases v <;> simp only [combinedIds] <;> first | exact separate _ | omega
  have firstFrame : Frame before.nextObject before middle [ids InitVar.i]:=
    ApplicationBirthFrame.declare_frame before.nextObject _ well (le_refl _) declared
  have secondFrame : Frame before.nextObject middle after [ids InitVar.i]:=
    ApplicationBirthFrame.store_frame before.nextObject _ wm firstFrame.fresh (by simp [scalarPointer,combinedIds]) written
  exact ⟨after,before.nextObject,.cons (.declareSome computed declared) (.cons reset .nil),post,firstFrame.trans secondFrame,le_refl _⟩

#print axioms initialize_drop
end RH080Next.FFTPV.DropTwoSource
