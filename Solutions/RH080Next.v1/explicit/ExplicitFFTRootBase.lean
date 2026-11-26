/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTDivideSource
import ExplicitFFTRootEvery
import FFTMultiplySmallFrame
import FFTZeroSliceCall
import FFTPairedIntModel
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.RootSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings
open IncrementSource (base)

/-- Actual initializer layout. Both pointer arguments may be proper slices of
one caller allocation, as in root=work+128 in the actual 512-word workspace. -/
structure Layout where
  object : Nat
  size : Nat
  rootStart : Nat
  workStart : Nat
  workBound : workStart+80 ≤ size
  rootBound : rootStart+12 ≤ size
  separate : rootStart+12 ≤ workStart ∨ workStart+80 ≤ rootStart

structure Input where
  layout : Layout
  old : Nat → Nat
  n : Nat
  positive : 0 < n
  small : n < base

inductive Param where | root | n | work deriving DecidableEq

def paramName : Param → String | .root=>"root" | .n=>"n" | .work=>"work"
def paramType : Param → CType | .root | .work=>.pointer .u64 | .n=>.u64

def paramValue (input : Input) : Param → Value
  | .root=>.pointer (wordPointer input.layout.object input.layout.rootStart)
  | .n=>.integer (integer64 input.n)
  | .work=>.pointer (wordPointer input.layout.object input.layout.workStart)

def paramIds (first : Nat) : Param → Nat | .root=>first | .n=>first+1 | .work=>first+2

structure ParamView {F : Type} (state : State F) (input : Input) (owner : Nat)
    (ids : Param → Nat) (data : Nat → Nat) : Prop where
  array : WordArrayRep state input.layout.object input.layout.size data
  locals : Locals state paramName paramType ids owner (paramValue input)
  separate : ∀v,input.layout.object≠ids v
  well : WellScoped state

/-- The original five literal base-10^9 limbs, not an assumed pi value. -/
def piDigit : Nat → Nat | 0=>279502884 | 1=>462643383 | 2=>589793238 | 3=>141592653 | 4=>3 | _=>0

def piData (old : Nat → Nat) (start : Nat) : Nat → (Nat → Nat)
  | 0=>ZeroSlice.zeroData old start 80
  | j+1=>Function.update (piData old start j) (start+j) (piDigit j)

theorem piDigit_bound (j : Nat) : piDigit j < base := by
  rcases j with _|_|_|_|_|j <;> simp only [piDigit] <;> norm_num [base]

theorem piData_processed (old : Nat → Nat) (start j k : Nat) (hk : k<j) :
    piData old start j (start+k)=piDigit k := by
  induction j with
  | zero=>omega
  | succ j ih=>
    by_cases same : k=j
    · subst k; simp [piData]
    · have different : start+k≠start+j:=by omega
      simpa only [piData,Function.update_of_ne different] using ih (by omega)

theorem piData_outside (old : Nat → Nat) (start j k : Nat)
    (outside : ¬(start≤k ∧ k<start+j)) :
    piData old start j k=ZeroSlice.zeroData old start 80 k := by
  induction j with
  | zero=>rfl
  | succ j ih=>
    have different : k≠start+j:=by omega
    simpa only [piData,Function.update_of_ne different] using ih (by omega)

theorem piData_value (old : Nat → Nat) (start : Nat) :
    FFT.Limbs.magnitude base 5 (fun i=>piData old start 5 (start+i))=
      FFT.IntegerModel.piInteger.toNat := by
  unfold FFT.Limbs.magnitude
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
  rw [piData_processed old start 5 0 (by omega),piData_processed old start 5 1 (by omega),
    piData_processed old start 5 2 (by omega),piData_processed old start 5 3 (by omega),
    piData_processed old start 5 4 (by omega)]
  norm_num [piDigit,base,FFT.IntegerModel.piInteger]
  rfl

/-- The original parameters are allocated by the actual application function,
not postulated as an initialized application state. -/
theorem initialize_parameters {F : Type} {entry : State F} (input : Input)
    (well : WellScoped entry) (empty : entry.environment=[])
    (rep : WordArrayRep entry input.layout.object input.layout.size input.old) :
    ∃sr sn sw,
      entry.declare (.pointer .u64) "root" (some (paramValue input .root))=some sr ∧
      sr.declare .u64 "n" (some (paramValue input .n))=some sn ∧
      sn.declare (.pointer .u64) "work" (some (paramValue input .work))=some sw ∧
      ParamView sw input entry.scope (paramIds entry.nextObject) input.old := by
  have hn64 : input.n<2^64:=lt_trans input.small (by norm_num [base])
  obtain ⟨sr,dr⟩:=ZeroFrame.declare_exists well _ "root" _
    (CompareSource.pointer_storable input.layout.object input.layout.rootStart)
  have wr:=wellScoped_declare well dr
  obtain ⟨sn,dn⟩:=ZeroFrame.declare_exists wr _ "n" _ (ZeroFrame.u64_storable input.n hn64)
  have wn:=wellScoped_declare wr dn
  obtain ⟨sw,dw⟩:=ZeroFrame.declare_exists wn _ "work" _
    (CompareSource.pointer_storable input.layout.object input.layout.workStart)
  have ir:=declare_storable (CompareSource.pointer_storable input.layout.object input.layout.rootStart)
    (CompareSource.pointer_storable input.layout.object input.layout.rootStart).converted dr
  have inn:=declare_storable (ZeroFrame.u64_storable input.n hn64) (convert64 input.n hn64) dn
  have iw:=declare_storable (CompareSource.pointer_storable input.layout.object input.layout.workStart)
    (CompareSource.pointer_storable input.layout.object input.layout.workStart).converted dw
  have no0:=ir.nextObject
  have no1:=inn.nextObject
  have sc0:=ir.scope
  have sc1:=inn.scope
  have live:=well.objectIds _ _ rep.2.1
  have params : Declarations entry sw:=.cons dr (.cons dn (.cons dw (.nil sw)))
  have words : WordArrayRep sw input.layout.object input.layout.size input.old:=by
    refine ⟨params.fields.2.2.2.1.trans rep.1,?_,rep.2.2⟩
    rw [params.fields.2.2.2.2 _ live]; exact rep.2.1
  have locals : Locals sw paramName paramType (paramIds entry.nextObject) entry.scope (paramValue input):=by
    constructor
    · intro v
      cases v <;> simp [paramName,paramType,paramIds,iw.environment,inn.environment,ir.environment,empty,no0,no1,List.lookup]
    · intro v
      cases v with
      | root=>
        have first:=ApplicationBirthFrame.slot_declare_old wr ir.slot inn
        have last:=ApplicationBirthFrame.slot_declare_old wn first iw
        simpa only [paramType,paramIds,paramValue] using last
      | n=>
        have last:=ApplicationBirthFrame.slot_declare_old wn inn.slot iw
        simpa only [paramType,paramIds,paramValue,no0,sc0] using last
      | work=>simpa only [paramType,paramIds,paramValue,no0,no1,sc0,sc1] using iw.slot
    · intro v w same
      cases v <;> cases w <;> simp_all [paramIds] <;> omega
    · rw [iw.nextScope,inn.nextScope,ir.nextScope]; exact well.current
  exact ⟨sr,sn,sw,dr,dn,dw,words,locals,(by intro v;cases v <;> simp only [paramIds] <;> omega),wellScoped_declare wn dw⟩

#print axioms piData_value
#print axioms initialize_parameters
end RH080Next.FFTPV.RootSource
