/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTComplexCallUnique
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.ComplexSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings ApplicationBirthFrame

def arguments (input : Input) : List Value:=
  [.pointer (wordPointer (input.layout.object .output) (input.layout.start .output)),
    .pointer (wordPointer (input.layout.object .a) (input.layout.start .a)),
    .pointer (wordPointer (input.layout.object .b) (input.layout.start .b)),
    .pointer (wordPointer (input.layout.object .work) (input.layout.start .work))]

def pair (data : Nat→Nat) (start : Nat) : Int×Int:=
  (CanonicalSource.represented data start,CanonicalSource.represented data (start+6))

def resultPair (input : Input) : Int×Int:=(sumValue input 0,sumValue input 1)

def Correct {F : Type} (context : Context F) (before : State F) (input : Input) : Prop:=
  ∃after workData outData,Call context "complex_multiply" (arguments input) before (.value (.integer (integer64 0))) after ∧
    WordArrayRep after (input.layout.object .output) (input.layout.length (input.layout.object .output)) outData ∧
    WordArrayRep after (input.layout.object .work) (input.layout.length (input.layout.object .work)) workData ∧
    pair outData (input.layout.start .output)=resultPair input ∧
    (∀c : Fin 2,∀k,k<5 → outData (input.layout.start .output+6*c.val+k)<1000000000) ∧
    (∀c : Fin 2,outData (input.layout.start .output+6*c.val+5)≤1) ∧
    (∀k,k< input.layout.length (input.layout.object .work) →
      (k< input.layout.start .work ∨ input.layout.start .work+46≤k) →
      (input.layout.object .work≠input.layout.object .output ∨ k< input.layout.start .output ∨ input.layout.start .output+12≤k) →
      workData k=input.old (input.layout.object .work) k) ∧
    (∀k,k< input.layout.length (input.layout.object .output) →
      (k< input.layout.start .output ∨ input.layout.start .output+12≤k) →
      (input.layout.object .output≠input.layout.object .work ∨ k< input.layout.start .work ∨ input.layout.start .work+46≤k) →
      outData k=input.old (input.layout.object .output) k) ∧
    MultiplyCall.CallerFrame before after [input.layout.object .output,input.layout.object .work] ∧
    ∀after' result,Call context "complex_multiply" (arguments input) before result after' →
      result=.value (.integer (integer64 0)) ∧ after'=after

theorem word_array_leave {F : Type} {state : State F} {object size : Nat} {data : Nat→Nat}
    (rep : WordArrayRep state object size data) (owner restore : Nat) (env : List (String×Pointer)) :
    WordArrayRep {state.leaveScope owner env with scope:=restore} object size data:=by
  refine ⟨rep.1,?_,rep.2.2⟩
  change (state.objects object).map _=some (wordObject size data)
  rw [rep.2.1]
  rfl

/-- The complete actual complex_multiply Call refines four Euclidean signed
products and the two exact signed additions. Application initialization,
argument orders, memory lifetimes, scratch/output slice frames and all
permitted complete Calls are proved from the actual source body. -/
theorem complex_multiply_correct {F : Type} (context : Context F)
    (selected : findFunction context.program "complex_multiply"=some complex_multiply_ast)
    (multiplySelected : findFunction context.program "fixed_multiply"=some fixed_multiply_ast)
    (zeroSelected : findFunction context.program "zero_words"=some zero_words_ast)
    (incSelected : findFunction context.program "increment_words"=some increment_words_ast)
    (addSelected : findFunction context.program "fixed_add"=some fixed_add_ast)
    (compareSelected : findFunction context.program "magnitude_compare"=some magnitude_compare_ast)
    (canonSelected : findFunction context.program "canonical_sign"=some FFTRecursivePV.canonical_sign_ast)
    (caller : State F) (input : Input) (well : WellScoped caller)
    (rep : ∀r,WordArrayRep caller (input.layout.object r) (input.layout.length (input.layout.object r)) (input.old (input.layout.object r))) :
    Correct context caller input:=by
  let entry : State F:={caller.enterScope with environment:=[]}
  obtain ⟨entered,middle,statusId,workData,outData,binding,whole,post,bodyFrame,scope,everyBody⟩:=
    function_body_execution context multiplySelected zeroSelected incSelected addSelected compareSelected canonSelected caller input well rep
  let after : State F:={middle.leaveScope entered.scope caller.environment with scope:=caller.scope}
  have called : Call context "complex_multiply" (arguments input) caller (.value (.integer (integer64 0))) after:=by
    apply Call.internal (function:=complex_multiply_ast) (entered:=entered) (middle:=middle)
      selected actual_body binding
    · exact Body.finish whole (by intro label impossible;cases impossible)
    · exact convert64 0 (by norm_num)
    · rfl
  have afterFrame : MultiplyCall.CallerFrame caller after [input.layout.object .output,input.layout.object .work]:=by
    refine ⟨rfl,rfl,?_,bodyFrame.fresh,bodyFrame.nextObject,bodyFrame.nextScope,bodyFrame.mode,bodyFrame.foreign,?_⟩
    · apply wellScoped_scope (wellScoped_leave bodyFrame.well entered.scope caller.environment)
      have current:=well.current
      have mono:=bodyFrame.nextScope
      change caller.scope<middle.nextScope
      omega
    · intro id old outside
      change (middle.objects id).map _=caller.objects id
      rw [bodyFrame.outside id old outside]
      cases present : caller.objects id with
      | none=>rfl
      | some object=>
        have different : object.storage≠.automatic entered.scope:=by
          intro equal
          rw [scope] at equal
          have bad:=well.automatic id object caller.nextScope present equal
          omega
        simp [different]
  have uniqueBody : ∀{x y : State F}{fx fy : Flow},
      Body context functionStatements entered functionStatements fx x →
      Body context functionStatements entered functionStatements fy y →fx=fy ∧ x=y:=by
    intro x y fx fy first second
    obtain ⟨xf,xs⟩:=everyBody x fx first
    obtain ⟨yf,ys⟩:=everyBody y fy second
    exact ⟨xf.trans yf.symm,xs.trans ys.symm⟩
  have real:=post.components (0:Fin 2) (by decide)
  have imaginary:=post.components (1:Fin 2) (by decide)
  have outputValue : pair outData (input.layout.start .output)=resultPair input:=by
    apply Prod.ext
    · simpa [pair,resultPair] using real.1
    · simpa [pair,resultPair] using imaginary.1
  refine ⟨after,workData,outData,called,word_array_leave post.output _ _ _,word_array_leave post.work _ _ _,
    outputValue,fun c k hk=>(post.components c c.isLt).2.1 k hk,fun c=>(post.components c c.isLt).2.2,
    post.outsideWork,post.outsideOutput,afterFrame,?_⟩
  intro after' result actual
  exact returned_call_unique_at selected binding uniqueBody called actual

#print axioms complex_multiply_correct
end RH080Next.FFTPV.ComplexSource
