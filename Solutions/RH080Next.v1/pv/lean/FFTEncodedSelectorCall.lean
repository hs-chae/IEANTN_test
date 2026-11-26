/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTEncodedSelectorBody
import FFTFixedMultiplyFrame
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.EncodedSelector
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings ApplicationBirthFrame

theorem returned_call_unique {F : Type} {context : Context F} (length fallback : Nat) (tree : Tree)
    (selected : findFunction context.program "encoded_node"=some (function length fallback tree))
    {before a b : State F} {args : List Value} {value : Value} {result : CallResult}
    (first : Call context "encoded_node" args before (.value value) a)
    (second : Call context "encoded_node" args before result b) : result=.value value ∧ b=a := by
  cases first with
  | external absent named foreign=>rw [selected] at absent; cases absent
  | internal selectedA shapeA paramsA bodyA convertA finishA=>
    have functionA:=Option.some.inj (selected.symm.trans selectedA)
    subst_vars
    have statementsA : (body length fallback tree)=_:=Stmt.block.inj ((actual_body length fallback tree).symm.trans shapeA)
    subst_vars
    cases second with
    | external absent named foreign=>rw [selected] at absent; cases absent
    | internal selectedB shapeB paramsB bodyB convertB finishB=>
      have functionB:=Option.some.inj (selected.symm.trans selectedB)
      subst_vars
      have statementsB : (body length fallback tree)=_:=Stmt.block.inj ((actual_body length fallback tree).symm.trans shapeB)
      subst_vars
      have enteredEq:=Option.some.inj (paramsA.symm.trans paramsB)
      subst_vars
      obtain ⟨flowEq,middleEq⟩:=body_unique length fallback tree bodyA bodyB
      cases flowEq
      cases middleEq
      have valueEq:=Option.some.inj (convertA.symm.trans convertB)
      cases valueEq
      exact ⟨rfl,rfl⟩
    | internalVoid selectedB shapeB void paramsB bodyB finishB=>
      have functionB:=Option.some.inj (selected.symm.trans selectedB)
      subst_vars
      cases void
    | internalTerminated selectedB shapeB paramsB bodyB=>
      have functionB:=Option.some.inj (selected.symm.trans selectedB)
      subst_vars
      have statementsB : (body length fallback tree)=_:=Stmt.block.inj ((actual_body length fallback tree).symm.trans shapeB)
      subst_vars
      have enteredEq:=Option.some.inj (paramsA.symm.trans paramsB)
      subst_vars
      cases (body_unique length fallback tree bodyA bodyB).1
  | internalVoid selectedA shapeA void paramsA bodyA finishA=>
    have functionA:=Option.some.inj (selected.symm.trans selectedA)
    subst_vars
    cases void

/-- Real scalar parameter allocation and the complete typed selector source
Call. All old caller objects, variables and foreign state are framed. -/
theorem encoded_node_call {F : Type} (context : Context F) (length fallback : Nat) (tree : Tree)
    (selected : findFunction context.program "encoded_node"=some (function length fallback tree))
    (caller : State F) (j : Nat) (lengthFits : length<2^64) (fallbackFits : fallback<2^64)
    (safe : tree.Safe) (well : WellScoped caller) (fits : j<2^64) :
    ∃after,Call context "encoded_node" [.integer (integer64 j)] caller
      (.value (.integer (integer64 (result length fallback tree j)))) after ∧
      MultiplyCall.CallerFrame caller after [] ∧
      ∀after' output,Call context "encoded_node" [.integer (integer64 j)] caller output after' →
        output=.value (.integer (integer64 (result length fallback tree j))) ∧ after'=after:=by
  let entry : State F:={caller.enterScope with environment:=[]}
  have we : WellScoped entry:=wellScoped_environment (wellScoped_enter well) []
  obtain ⟨entered,declared⟩:=ZeroFrame.declare_exists we .u64 "j" (.integer (integer64 j)) (ZeroFrame.u64_storable j fits)
  have dj : Declaration entry entered "j" .u64 (.integer (integer64 j)):=
    declare_storable (ZeroFrame.u64_storable j fits) (by simpa only using convert64 j fits) declared
  have lookup : entered.environment.lookup "j"=some (scalarPointer entry.nextObject .u64):=by
    rw [dj.environment]
    simp [List.lookup]
  obtain ⟨middle,run,effect⟩:=body_execution context length fallback tree entered entry.nextObject entry.scope j
    lengthFits fallbackFits safe (wellScoped_declare we declared) lookup dj.slot fits
  have binding : bindParameters entry (function length fallback tree).parameters [.integer (integer64 j)]=some entered:=by
    simp [function,bindParameters,declared]
  let after : State F:={middle.leaveScope entered.scope caller.environment with scope:=caller.scope}
  have called : Call context "encoded_node" [.integer (integer64 j)] caller
      (.value (.integer (integer64 (result length fallback tree j)))) after:=by
    apply Call.internal (function:=function length fallback tree) (entered:=entered) (middle:=middle)
      selected (actual_body length fallback tree) binding
    · exact Body.finish run (by intro label impossible;cases impossible)
    · exact convert64 _ (result_fits length fallback tree j fallbackFits safe)
    · rfl
  have clocks:=effect.metadata
  have callerFrame : MultiplyCall.CallerFrame caller after []:=by
    refine ⟨rfl,rfl,?_,?_,?_,?_,?_,?_,?_⟩
    · apply wellScoped_scope (wellScoped_leave clocks.well entered.scope caller.environment)
      have current:=well.current
      have ns:=dj.nextScope
      have mono:=clocks.nextScope
      change entered.nextScope=caller.nextScope+1 at ns
      change caller.scope<middle.nextScope
      omega
    · have no:=dj.nextObject
      have same:=clocks.nextObject
      change entered.nextObject=caller.nextObject+1 at no
      change caller.nextObject≤middle.nextObject
      omega
    · have no:=dj.nextObject
      have same:=clocks.nextObject
      change entered.nextObject=caller.nextObject+1 at no
      change caller.nextObject≤middle.nextObject
      omega
    · have ns:=dj.nextScope
      have mono:=clocks.nextScope
      change entered.nextScope=caller.nextScope+1 at ns
      change caller.nextScope≤middle.nextScope
      omega
    · exact clocks.mode.trans dj.mode
    · exact clocks.foreign.trans ((declare_foreign declared).trans (show entry.foreign=caller.foreign from rfl))
    · intro id old outside
      change (middle.objects id).map _=caller.objects id
      rw [effect.objects,dj.outside id (by change id≠caller.nextObject;omega)]
      change (caller.objects id).map _=caller.objects id
      cases present : caller.objects id with
      | none=>rfl
      | some object=>
        have different : object.storage≠.automatic entered.scope:=by
          intro equal
          rw [dj.scope] at equal
          have invalid:=well.automatic id object caller.nextScope present equal
          omega
        simp [different]
  refine ⟨after,called,callerFrame,?_⟩
  intro after' output other
  exact returned_call_unique length fallback tree selected called other

#print axioms encoded_node_call
#print axioms returned_call_unique
end RH080Next.FFTPV.EncodedSelector
