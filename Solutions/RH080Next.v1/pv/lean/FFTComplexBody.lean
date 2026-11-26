/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTComplexSums
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.ComplexSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings ApplicationBirthFrame

theorem append_exec {F : Type} {context : Context F} {before middle after : State F}
    {xs ys : List Stmt} {flow : Flow} (first : ExecList context before xs .normal middle)
    (second : ExecList context middle ys flow after) : ExecList context before (xs++ys) flow after:=by
  induction xs generalizing before with
  | nil=>cases first;exact second
  | cons x xs ih=>
    cases first with
    | cons run rest=>exact .cons run (ih rest)
    | abrupt run ne=>exact False.elim (ne rfl)

theorem decompose_exec {F : Type} {context : Context F} {before after : State F}
    {xs ys : List Stmt} {flow : Flow} (run : ExecList context before (xs++ys) flow after) :
    (∃middle,ExecList context before xs .normal middle ∧ ExecList context middle ys flow after) ∨
      (ExecList context before xs flow after ∧ flow≠.normal):=by
  induction xs generalizing before with
  | nil=>exact Or.inl ⟨before,.nil,run⟩
  | cons x xs ih=>
    cases run with
    | cons head tail=>
      rcases ih tail with ⟨middle,leading,rest⟩|⟨leading,ne⟩
      · exact Or.inl ⟨middle,.cons head leading,rest⟩
      · exact Or.inr ⟨.cons head leading,ne⟩
    | abrupt head ne=>exact Or.inr ⟨.abrupt head ne,ne⟩

theorem consume_normal_prefix {F : Type} {context : Context F} {before middle after : State F}
    {xs ys : List Stmt} {flow : Flow}
    (post : ∀other f,ExecList context before xs f other →f=.normal ∧ other=middle)
    (run : ExecList context before (xs++ys) flow after) : ExecList context middle ys flow after:=by
  rcases decompose_exec run with ⟨current,leading,tail⟩|⟨leading,ne⟩
  · have same:=(post _ _ leading).2
    cases same
    exact tail
  · exact False.elim (ne (post _ _ leading).1)

theorem frame_weaken {F : Type} {a b : State F} {oldCutoff newCutoff : Nat} {oldWrites newWrites : List Nat}
    (frame : Frame oldCutoff a b oldWrites) (cutoff : newCutoff≤oldCutoff)
    (writes : ∀id,id∉newWrites →id∉oldWrites) : Frame newCutoff a b newWrites:=
  ⟨frame.well,cutoff.trans frame.fresh,frame.nextObject,frame.nextScope,frame.mode,frame.foreign,
    fun id old outside=>frame.outside id (old.trans_le cutoff) (writes id outside)⟩

def returnStatus : Stmt:=.returnValue (some (.variable "status"))

theorem actual_statements : functionStatements=[statusDeclaration]++productStatements++sumStatements++[returnStatus]:=by rfl

/-- The complete actual eight-statement complex function body: all real
parameter declarations, scalar products, signed additions and final return.
Its universal postcondition covers every operational execution. -/
theorem function_body_execution {F : Type} (context : Context F)
    (multiplySelected : findFunction context.program "fixed_multiply"=some fixed_multiply_ast)
    (zeroSelected : findFunction context.program "zero_words"=some zero_words_ast)
    (incSelected : findFunction context.program "increment_words"=some increment_words_ast)
    (addSelected : findFunction context.program "fixed_add"=some fixed_add_ast)
    (compareSelected : findFunction context.program "magnitude_compare"=some magnitude_compare_ast)
    (canonSelected : findFunction context.program "canonical_sign"=some FFTRecursivePV.canonical_sign_ast)
    (caller : State F) (input : Input) (well : WellScoped caller)
    (rep : ∀r,WordArrayRep caller (input.layout.object r) (input.layout.length (input.layout.object r)) (input.old (input.layout.object r))) :
    let entry : State F:={caller.enterScope with environment:=[]}
    ∃entered middle statusId finalWork finalOut,
      bindParameters entry complex_multiply_ast.parameters
        [.pointer (wordPointer (input.layout.object .output) (input.layout.start .output)),
          .pointer (wordPointer (input.layout.object .a) (input.layout.start .a)),
          .pointer (wordPointer (input.layout.object .b) (input.layout.start .b)),
          .pointer (wordPointer (input.layout.object .work) (input.layout.start .work))]=some entered ∧
      ExecList context entered functionStatements (.returned (.integer (integer64 0))) middle ∧
      SumView middle input (pIds entry.nextObject) entry.scope statusId 2 finalWork finalOut ∧
      Frame caller.nextObject caller middle [input.layout.object .output,input.layout.object .work] ∧ entered.scope=entry.scope ∧
      ∀after flow,Body context functionStatements entered functionStatements flow after →
        flow=.returned (.integer (integer64 0)) ∧ after=middle:=by
  dsimp only
  obtain ⟨entered,s0,statusId,binding,init,h0,initialFrame,scope⟩:=initialize_view context caller input well rep
  obtain ⟨s1,w1,products,h1,productFrame,productsEvery⟩:=
    product_statements_execution context multiplySelected zeroSelected incSelected canonSelected h0
  obtain ⟨middle,finalWork,finalOut,sums,h2,sumFrame,sumsEvery⟩:=
    sum_statements_execution context addSelected compareSelected canonSelected h1.toSumView
  have returned : Exec context middle returnStatus (.returned (.integer (integer64 0))) middle:=
    .returnSome (.variable h2.statusLookup h2.statusSlot.read)
  have last : ExecList context middle [returnStatus] (.returned (.integer (integer64 0))) middle:=.abrupt returned (by simp)
  have whole : ExecList context entered functionStatements (.returned (.integer (integer64 0))) middle:=by
    have joined:=append_exec (xs:=[statusDeclaration]) (ys:=productStatements++(sumStatements++[returnStatus]))
      (.cons init .nil) (append_exec products (append_exec sums last))
    simpa only [actual_statements,List.append_assoc] using joined
  have firstFrame : Frame caller.nextObject caller s0 [input.layout.object .output,input.layout.object .work]:=
    frame_weaken initialFrame le_rfl (by simp)
  have secondFrame : Frame caller.nextObject s0 s1 [input.layout.object .output,input.layout.object .work]:=
    frame_weaken productFrame.frame initialFrame.nextObject (by intro id outside;simp_all)
  have thirdFrame : Frame caller.nextObject s1 middle [input.layout.object .output,input.layout.object .work]:=
    frame_weaken sumFrame.frame (initialFrame.nextObject.trans productFrame.frame.nextObject) (by intro id outside;simp_all)
  refine ⟨entered,middle,statusId,finalWork,finalOut,binding,whole,h2,(firstFrame.trans secondFrame).trans thirdFrame,scope,?_⟩
  have initEvery : ∀after flow,Exec context entered statusDeclaration flow after →flow=.normal ∧ after=s0:=by
    intro after flow other
    have unique:=PureDeterminism.simple_unique (by simp [statusDeclaration,PureDeterminism.Simple,SourcePure.CallFree]) init other
    exact ⟨unique.1.symm,unique.2.symm⟩
  have lastUnique : ∀s∈[returnStatus],CompareSource.Unique context s:=by
    intro s member
    have same : s=returnStatus:=by simpa using member
    subst s
    intro before a b fa fb first second
    exact PureDeterminism.simple_unique (by simp [returnStatus,PureDeterminism.Simple,SourcePure.CallFree]) first second
  intro after flow actual
  cases actual with
  | finish run _=>
    have run0:=consume_source_head initEvery run
    have run1 : ExecList context s1 (sumStatements++[returnStatus]) flow after:=
      consume_normal_prefix productsEvery run0
    have run2 : ExecList context middle [returnStatus] flow after:=consume_normal_prefix sumsEvery run1
    exact CompareSource.list_unique lastUnique run2 last
  | jump run target rest=>simp [functionStatements,statusDeclaration,StatusCall.statement,labelTail] at target

#print axioms function_body_execution
end RH080Next.FFTPV.ComplexSource
