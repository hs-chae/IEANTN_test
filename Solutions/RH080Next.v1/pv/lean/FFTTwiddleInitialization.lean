/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTTwiddleGuards
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.TwiddleSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings
open ApplicationBirthFrame

inductive InitVar where | n | twiddle | root | work | status deriving DecidableEq

def lift : InitVar→Var | .n=>.n | .twiddle=>.twiddle | .root=>.root | .work=>.work | .status=>.status

def combinedIds (old : InitVar→Nat) (newId : Nat) : Var→Nat
  | .n=>old .n | .twiddle=>old .twiddle | .root=>old .root | .work=>old .work | .status=>old .status | .j=>newId

def unitTable : Nat→Nat:=Function.update (fun _=>0) 4 1

def unitAssignment : Stmt:=.assign (.index (.variable "twiddle") (.literal (.integer 4 "ULL"))) (.literal (.integer 1 "ULL"))
def jDeclaration : Stmt:=.declare .u64 "j" (some (.literal (.integer 1 "ULL")))

theorem actual_unit_assignment : (ProductRow.items FFTRecursivePV.w4_recursive_norm_upper_ast.body)[17]?=some unitAssignment := by rfl
theorem actual_j_declaration : (ProductRow.items FFTRecursivePV.w4_recursive_norm_upper_ast.body)[18]?=some jDeclaration := by rfl

theorem unit_table_pair : ComplexSource.pair unitTable 0=(10^36,0) := by
  norm_num [ComplexSource.pair,CanonicalSource.represented,FFT.Limbs.magnitude,Finset.sum_range_succ,
    FFT.Limbs.signed,unitTable,Function.update]

/-- The initial unit twiddle and the real j=1 local are constructed by the
actual store/declaration. Exact mathematical recurrence bounds discharge
all subsequent source multiplication guards for the two original grids. -/
theorem initialize_table {F : Type} (context : Context F) (before : State F)
    (tableObject workObject n : Nat) (oldIds : InitVar→Nat) (workData : Nat→Nat)
    (original : n=131072 ∨ n=16777216) (well : WellScoped before)
    (locals : Locals before (fun v=>name (lift v)) (fun v=>type (lift v)) oldIds before.scope
      (fun v=>values tableObject workObject n 0 (lift v)))
    (table : WordArrayRep before tableObject (n/2*12) (fun _=>0))
    (work : WordArrayRep before workObject 512 workData) (different : tableObject≠workObject)
    (rootDigits : ∀c : Fin 2,∀d,d<5 → workData (128+6*c.val+d)<1000000000)
    (rootSigns : ∀c : Fin 2,workData (128+6*c.val+5)≤1)
    (rootValue : ComplexSource.pair workData 128=FFT.IntegerModel.root n) :
    ∃after newId,ExecList context before [unitAssignment,jDeclaration] .normal after ∧
      View after tableObject workObject n (combinedIds oldIds newId) before.scope 1 unitTable workData (FFT.IntegerModel.root n) ∧
      Frame before.nextObject before after [tableObject] ∧ before.nextObject≤newId := by
  have nb : 2≤n ∧ n≤16777216 := by rcases original with rfl|rfl <;> norm_num
  have tableBound : 4<n/2*12 := by omega
  have separates : ∀v,tableObject≠oldIds v ∧ workObject≠oldIds v := by
    intro v
    exact ⟨MultiplyParameters.array_slot_different table (locals.slots v),MultiplyParameters.array_slot_different work (locals.slots v)⟩
  obtain ⟨middle,stored,tableMiddle⟩:=word_store_with_rep table tableBound (by norm_num : 1<2^64)
  have middleWell:=wellScoped_store well stored
  have storeFields:=SourceLocals.store_frame stored
  have params:=ApplicationBirthFrame.locals_store_other locals (fun v=>(separates v).1.symm) stored
  have workMiddle : WordArrayRep middle workObject 512 workData :=
    ⟨storeFields.2.1.trans work.1,(storeFields.2.2.2.2.2 workObject different.symm).trans work.2.1,work.2.2⟩
  have storeRun : Exec context before unitAssignment .normal middle := by
    apply Exec.assign (value:=.integer (integer64 1)) (.literal (.integer 1 "ULL") _ _ (by rfl))
      (.index (.variable (locals.lookup InitVar.twiddle) (locals.read InitVar.twiddle))
        (.literal (.integer 4 "ULL") _ (.integer (integer64 4)) (by rfl))
        (slice_pointer_add table (start:=0) (i:=4) (by simpa using tableBound)))
    exact stored
  obtain ⟨after,declared⟩:=ZeroFrame.declare_exists middleWell .u64 "j" (.integer (integer64 1)) (ZeroFrame.u64_storable 1 (by norm_num))
  have birth:=declare_storable (ZeroFrame.u64_storable 1 (by norm_num)) (by rfl) declared
  have oldParam:=ApplicationBirthFrame.locals_declare_old middleWell params (by intro v;cases v <;> decide) birth
  have oldTable : tableObject<middle.nextObject:=middleWell.objectIds _ _ tableMiddle.2.1
  have oldWork : workObject<middle.nextObject:=middleWell.objectIds _ _ workMiddle.2.1
  have ps : Locals after name type (combinedIds oldIds middle.nextObject) before.scope (values tableObject workObject n 1) := by
    constructor
    · intro v
      cases v with
      | j=>simp [combinedIds,name,type,scalarPointer,List.lookup,birth.environment]
      | n=>exact oldParam.lookup InitVar.n
      | twiddle=>exact oldParam.lookup InitVar.twiddle
      | root=>exact oldParam.lookup InitVar.root
      | work=>exact oldParam.lookup InitVar.work
      | status=>exact oldParam.lookup InitVar.status
    · intro v
      cases v with
      | j=>simpa only [combinedIds,type,values,storeFields.2.2.1] using birth.slot
      | n=>exact oldParam.slots InitVar.n
      | twiddle=>exact oldParam.slots InitVar.twiddle
      | root=>exact oldParam.slots InitVar.root
      | work=>exact oldParam.slots InitVar.work
      | status=>exact oldParam.slots InitVar.status
    · intro v w equal
      have oldBounds : ∀v,oldIds v<middle.nextObject:=fun v=>middleWell.objectIds _ _ (params.slots v).object
      have oldNe : ∀v w : InitVar,v≠w → oldIds v≠oldIds w := fun v w ne eq=>ne (locals.distinct eq)
      have bn:=oldBounds InitVar.n
      have bt:=oldBounds InitVar.twiddle
      have br:=oldBounds InitVar.root
      have bw:=oldBounds InitVar.work
      have bs:=oldBounds InitVar.status
      cases v <;> cases w <;> simp only [combinedIds] at equal ⊢
      all_goals first | rfl | exact False.elim (oldNe _ _ (by decide) equal) | omega
    · rw [birth.nextScope,storeFields.2.2.2.1]
      exact well.current
  have outTable : WordArrayRep after tableObject (n/2*12) unitTable := by
    refine ⟨birth.mode.trans tableMiddle.1,?_,tableMiddle.2.2⟩
    rw [birth.outside tableObject (by omega)]
    exact tableMiddle.2.1
  have outWork : WordArrayRep after workObject 512 workData:=
    ⟨birth.mode.trans workMiddle.1,(birth.outside workObject (by omega)).trans workMiddle.2.1,workMiddle.2.2⟩
  have post : View after tableObject workObject n (combinedIds oldIds middle.nextObject) before.scope 1 unitTable workData (FFT.IntegerModel.root n) := by
    refine ⟨ps,outTable,outWork,different,?_,nb,by omega,?_,?_,?_,rootDigits,rootSigns,rootValue,
      fixed_root_small n original,fun k hk=>fixed_values_small n original k hk,wellScoped_declare middleWell declared⟩
    · intro v
      cases v <;> simp only [combinedIds] <;> first
        | exact separates _
        | exact ⟨by omega,by omega⟩
    · intro k hk c d hd
      have ke : k=0:=by omega
      subst k
      fin_cases c <;> interval_cases d <;> norm_num [unitTable,Function.update]
    · intro k hk c
      have ke : k=0:=by omega
      subst k
      fin_cases c <;> norm_num [unitTable,Function.update]
    · intro k hk
      have ke : k=0:=by omega
      subst k
      exact unit_table_pair
  have firstFrame : Frame before.nextObject before middle [tableObject] :=
    ApplicationBirthFrame.store_frame before.nextObject [tableObject] well (le_refl _) (by simp [wordPointer]) stored
  have secondFrame : Frame before.nextObject middle after [tableObject] :=
    ApplicationBirthFrame.declare_frame before.nextObject [tableObject] middleWell firstFrame.fresh declared
  exact ⟨after,middle.nextObject,.cons storeRun (.cons (.declareSome (.literal (.integer 1 "ULL") _ _ (by rfl)) declared) .nil),post,firstFrame.trans secondFrame,by rw [storeFields.2.2.2.2.1]⟩

#print axioms actual_unit_assignment
#print axioms actual_j_declaration
#print axioms unit_table_pair
#print axioms initialize_table
end RH080Next.FFTPV.TwiddleSource
