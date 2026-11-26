/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTComplexProducts
import ExplicitFFTAddSlice
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.ComplexSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings

def leftProduct (part : Fin 2) : Fin 4:=if part.val=0 then 0 else 2
def rightProduct (part : Fin 2) : Fin 4:=if part.val=0 then 1 else 3

def sumValue (input : Input) (part : Fin 2) : Int:=
  if part.val=0 then productValue input 0-productValue input 1
  else productValue input 2+productValue input 3

def ComponentAt (input : Input) (outData : Nat→Nat) (part : Fin 2) : Prop:=
  CanonicalSource.represented outData (input.layout.start .output+6*part.val)=sumValue input part ∧
    (∀k,k<5 → outData (input.layout.start .output+6*part.val+k)<1000000000) ∧
    outData (input.layout.start .output+6*part.val+5)≤1

structure SumView {F : Type} (state : State F) (input : Input)
    (ids : PVar→Nat) (owner statusId stage : Nat) (workData outData : Nat→Nat) : Prop where
  params : Locals state pName pType ids owner
    (pValue (input.layout.object .output) (input.layout.start .output) (input.layout.object .a) (input.layout.start .a)
      (input.layout.object .b) (input.layout.start .b) (input.layout.object .work) (input.layout.start .work))
  statusLookup : state.environment.lookup "status"=some (scalarPointer statusId .u64)
  statusSlot : Slot state statusId owner .u64 (.integer (integer64 0))
  work : WordArrayRep state (input.layout.object .work) (input.layout.length (input.layout.object .work)) workData
  output : WordArrayRep state (input.layout.object .output) (input.layout.length (input.layout.object .output)) outData
  products : ∀i : Fin 4,ProductAt input workData i
  components : ∀part : Fin 2,part.val<stage →ComponentAt input outData part
  outsideWork : ∀k,k< input.layout.length (input.layout.object .work) →
    (k< input.layout.start .work ∨ input.layout.start .work+46≤k) →
    (input.layout.object .work≠input.layout.object .output ∨ k< input.layout.start .output ∨ input.layout.start .output+12≤k) →
    workData k=input.old (input.layout.object .work) k
  outsideOutput : ∀k,k< input.layout.length (input.layout.object .output) →
    (k< input.layout.start .output ∨ input.layout.start .output+12≤k) →
    (input.layout.object .output≠input.layout.object .work ∨ k< input.layout.start .work ∨ input.layout.start .work+46≤k) →
    outData k=input.old (input.layout.object .output) k
  active : stage≤2
  well : WellScoped state

theorem View.toSumView {F : Type} {state : State F} {input : Input}
    {ids : PVar→Nat} {owner statusId : Nat} {workData : Nat→Nat}
    (h : View state input ids owner statusId 4 workData) :
    SumView state input ids owner statusId 0 workData (dataAt input workData (input.layout.object .output)):=by
  refine ⟨h.params,h.statusLookup,h.statusSlot,?_,h.arrays .output,fun i=>h.products i i.isLt,?_,?_,?_,by omega,h.well⟩
  · simpa [dataAt] using h.arrays MultiplyParameters.Var.work
  · intro part impossible
    omega
  · intro k bound outsideWork outsideOutput
    exact h.outsideWork k bound outsideWork
  · intro k bound outsideOutput outsideWork
    by_cases same : input.layout.object .output=input.layout.object .work
    · have bound' : k< input.layout.length (input.layout.object .work):=by simpa only [same] using bound
      have outside : k< input.layout.start .work ∨ input.layout.start .work+46≤k:=by
        rcases outsideWork with no|low|high
        · exact False.elim (no same)
        · exact Or.inl low
        · exact Or.inr high
      simpa [dataAt,same] using h.outsideWork k bound' outside
    · simp only [dataAt,if_neg same]

def sumObject (layout : Layout) : AddSource.Array→Nat
  | .out=>layout.object .output | .a|.b=>layout.object .work

def sumStart (layout : Layout) (part : Fin 2) : AddSource.Array→Nat
  | .out=>layout.start .output+6*part.val
  | .a=>layout.start .work+6*(leftProduct part).val
  | .b=>layout.start .work+6*(rightProduct part).val

def sumLayout (input : Input) (part : Fin 2) : AddSource.Layout where
  object:=sumObject input.layout
  start:=sumStart input.layout part
  length:=input.layout.length
  bound:=by
    intro r
    have op:=input.layout.bound MultiplyParameters.Var.output
    have wp:=input.layout.bound MultiplyParameters.Var.work
    have pb:=part.isLt
    have lb:=(leftProduct part).isLt
    have rb:=(rightProduct part).isLt
    simp at op wp
    cases r <;> simp only [sumObject,sumStart] <;> omega
  safeA:=by
    have disjoint:=input.disjoint MultiplyParameters.Var.output (by decide)
    have pb:=part.isLt
    have lb:=(leftProduct part).isLt
    change AddSource.SafeAlias _ _ _ _
    unfold AddSource.SafeAlias
    simp only [sumObject,sumStart]
    rcases disjoint with no|low|high
    · exact Or.inl no
    · exact Or.inr (Or.inr (Or.inl (by omega)))
    · exact Or.inr (Or.inr (Or.inr (by omega)))
  safeB:=by
    have disjoint:=input.disjoint MultiplyParameters.Var.output (by decide)
    have pb:=part.isLt
    have rb:=(rightProduct part).isLt
    change AddSource.SafeAlias _ _ _ _
    unfold AddSource.SafeAlias
    simp only [sumObject,sumStart]
    rcases disjoint with no|low|high
    · exact Or.inl no
    · exact Or.inr (Or.inr (Or.inl (by omega)))
    · exact Or.inr (Or.inr (Or.inr (by omega)))

def sumData (input : Input) (workData outData : Nat→Nat) (object : Nat) : Nat→Nat:=
  if object=input.layout.object .output then outData else workData

theorem sum_data_work_rep {F : Type} {state : State F} {input : Input}
    {ids : PVar→Nat} {owner statusId stage : Nat} {workData outData : Nat→Nat}
    (h : SumView state input ids owner statusId stage workData outData) :
    WordArrayRep state (input.layout.object .work) (input.layout.length (input.layout.object .work))
      (sumData input workData outData (input.layout.object .work)):=by
  by_cases same : input.layout.object .work=input.layout.object .output
  · simpa [sumData,same] using h.output
  · simpa only [sumData,if_neg same] using h.work

theorem sum_data_work_value {F : Type} {state : State F} {input : Input}
    {ids : PVar→Nat} {owner statusId stage index : Nat} {workData outData : Nat→Nat}
    (h : SumView state input ids owner statusId stage workData outData)
    (bound : index< input.layout.length (input.layout.object .work)) :
    sumData input workData outData (input.layout.object .work) index=workData index:=
  word_data_unique (sum_data_work_rep h) h.work index bound

#print axioms sumLayout
#print axioms sum_data_work_value
end RH080Next.FFTPV.ComplexSource
