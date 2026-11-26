/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTComplexFrame
import FFTComplexModel
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.ComplexSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings ApplicationBirthFrame

structure Input where
  layout : Layout
  old : Nat→Nat→Nat
  disjoint : ∀r,r≠MultiplyParameters.Var.work →
    layout.object r≠layout.object .work ∨ layout.start r+12≤layout.start .work ∨
      layout.start .work+46≤layout.start r
  digits : ∀r,r=MultiplyParameters.Var.a ∨ r=MultiplyParameters.Var.b →
    ∀c : Fin 2,∀k,k<5 → old (layout.object r) (layout.start r+6*c.val+k)<1000000000
  signs : ∀r,r=MultiplyParameters.Var.a ∨ r=MultiplyParameters.Var.b →
    ∀c : Fin 2,old (layout.object r) (layout.start r+6*c.val+5)≤1
  magnitude : ∀r,r=MultiplyParameters.Var.a ∨ r=MultiplyParameters.Var.b →
    ∀c : Fin 2,FFT.Limbs.magnitude 1000000000 5
      (fun k=>old (layout.object r) (layout.start r+6*c.val+k))≤1000*unit

def dataAt (input : Input) (workData : Nat→Nat) (object : Nat) : Nat→Nat:=
  if object=input.layout.object .work then workData else input.old object

def productValue (input : Input) (i : Fin 4) : Int:=
  (CanonicalSource.represented (input.old (input.layout.object .a)) (input.layout.start .a+aOffset i)*
    CanonicalSource.represented (input.old (input.layout.object .b)) (input.layout.start .b+bOffset i))/(unit:Nat)

def ProductAt (input : Input) (workData : Nat→Nat) (i : Fin 4) : Prop:=
  CanonicalSource.represented workData (input.layout.start .work+6*i.val)=productValue input i ∧
    (∀k,k<5 → workData (input.layout.start .work+6*i.val+k)<1000000000) ∧
    workData (input.layout.start .work+6*i.val+5)≤1

structure View {F : Type} (state : State F) (input : Input)
    (ids : PVar→Nat) (owner statusId stage : Nat) (workData : Nat→Nat) : Prop where
  params : Locals state pName pType ids owner
    (pValue (input.layout.object .output) (input.layout.start .output) (input.layout.object .a) (input.layout.start .a)
      (input.layout.object .b) (input.layout.start .b) (input.layout.object .work) (input.layout.start .work))
  statusLookup : state.environment.lookup "status"=some (scalarPointer statusId .u64)
  statusSlot : Slot state statusId owner .u64 (.integer (integer64 0))
  arrays : ∀r,WordArrayRep state (input.layout.object r) (input.layout.length (input.layout.object r))
    (dataAt input workData (input.layout.object r))
  inputValues : ∀r,r=MultiplyParameters.Var.a ∨ r=MultiplyParameters.Var.b →
    ∀k,k<12 → dataAt input workData (input.layout.object r) (input.layout.start r+k)=input.old (input.layout.object r) (input.layout.start r+k)
  products : ∀i : Fin 4,i.val<stage → ProductAt input workData i
  outsideWork : ∀k,k< input.layout.length (input.layout.object .work) →
    (k< input.layout.start .work ∨ input.layout.start .work+46≤k) → workData k=input.old (input.layout.object .work) k
  active : stage≤4
  well : WellScoped state

/-- Real four-pointer binding and status birth establish the zero-stage
complex invariant from actual caller WordArrayRep inputs. No numerical result
or initialized callee state is assumed. -/
theorem initialize_view {F : Type} (context : Context F) (caller : State F) (input : Input)
    (well : WellScoped caller)
    (rep : ∀r,WordArrayRep caller (input.layout.object r) (input.layout.length (input.layout.object r)) (input.old (input.layout.object r))) :
    let entry : State F:={caller.enterScope with environment:=[]}
    ∃entered after statusId,
      bindParameters entry complex_multiply_ast.parameters
        [.pointer (wordPointer (input.layout.object .output) (input.layout.start .output)),
          .pointer (wordPointer (input.layout.object .a) (input.layout.start .a)),
          .pointer (wordPointer (input.layout.object .b) (input.layout.start .b)),
          .pointer (wordPointer (input.layout.object .work) (input.layout.start .work))]=some entered ∧
      Exec context entered statusDeclaration .normal after ∧
      View after input (pIds entry.nextObject) entry.scope statusId 0 (input.old (input.layout.object .work)) ∧
      Frame caller.nextObject caller after [] ∧ entered.scope=entry.scope:=by
  dsimp only
  obtain ⟨entered,after,statusId,bound,run,params,lookup,slot,frame,scope,idEq⟩:=initialize_call context caller
    (input.layout.object .output) (input.layout.start .output) (input.layout.object .a) (input.layout.start .a)
    (input.layout.object .b) (input.layout.start .b) (input.layout.object .work) (input.layout.start .work) well
  refine ⟨entered,after,statusId,bound,run,?_,frame,scope⟩
  refine ⟨params,lookup,slot,?_,?_,?_,fun _ _ _=>rfl,by omega,frame.well⟩
  · intro r
    have old:=well.objectIds _ _ (rep r).2.1
    have lifted : WordArrayRep after (input.layout.object r) (input.layout.length (input.layout.object r)) (input.old (input.layout.object r)):=
      ⟨frame.mode.trans (rep r).1,(frame.outside _ old (by simp)).trans (rep r).2.1,(rep r).2.2⟩
    have sameData : dataAt input (input.old (input.layout.object .work)) (input.layout.object r)=input.old (input.layout.object r):=by
      unfold dataAt
      split
      · rename_i same
        rw [same]
      · rfl
    rw [sameData]
    exact lifted
  · intro r role k hk
    unfold dataAt
    split
    · rename_i same
      rw [same]
    · rfl
  · intro i impossible
    omega

#print axioms initialize_view
end RH080Next.FFTPV.ComplexSource
