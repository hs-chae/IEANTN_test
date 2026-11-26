/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTFixedMultiplySuffixExecution
import FFTFixedMultiplySuffixDeterminism
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.MultiplySuffix
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots ProductInner

private theorem pure_ite_unique {F : Type} {context : Context F} {test : Expr} {yes : Stmt}
    (closed : SourcePure.CallFree test) (unique : CompareSource.Unique context yes) :
    CompareSource.Unique context (.ite test yes none) := by
  intro before a b fa fb first second
  cases first with
  | ifTrue ev truth body =>
    have state:=SourcePure.eval_state ev closed
    cases state
    cases second with
    | ifTrue ev' truth' body' =>
      obtain ⟨rfl,rfl⟩:=PureDeterminism.eval_unique closed ev ev'
      exact unique body body'
    | ifFalse ev' truth' =>
      cases (PureDeterminism.eval_unique closed ev ev').1
      simp_all
  | ifFalse ev truth =>
    have state:=SourcePure.eval_state ev closed
    cases state
    cases second with
    | ifTrue ev' truth' body' =>
      cases (PureDeterminism.eval_unique closed ev ev').1
      simp_all
    | ifFalse ev' truth' => exact ⟨rfl,(PureDeterminism.eval_unique closed ev ev').2⟩

private theorem sign_branch_unique {F : Type} (context : Context F) : CompareSource.Unique context signBranch := by
  apply pure_ite_unique (by simp [signCondition,v,lit,SourcePure.CallFree])
  intro before a b fa fb first second
  exact PureDeterminism.block_unique (by simp [v,lit,PureDeterminism.Simple,SourcePure.CallFree]) first second

private theorem canonical_expression_unique {F : Type} {context : Context F}
    (selected : findFunction context.program "canonical_sign"=some FFTRecursivePV.canonical_sign_ast) :
    CompareSource.Unique context canonicalCall := by
  intro before a b fa fb first second
  have closed : ∀e∈[v "out"],SourcePure.CallFree e := by simp [v,SourcePure.CallFree]
  cases first with
  | expression ev =>
    cases ev with
    | call args call =>
      cases second with
      | expression ev' =>
        cases ev' with
        | call args' call' =>
          obtain ⟨rfl,rfl,rfl⟩:=ApplicationPureCall.args_unique closed args args'
          obtain ⟨_,eq⟩:=CanonicalSource.call_unique selected call call'
          exact ⟨rfl,eq.symm⟩
        | load place loaded => cases place
      | callTerminated args' call' =>
        obtain ⟨rfl,rfl,rfl⟩:=ApplicationPureCall.args_unique closed args args'
        cases (CanonicalSource.call_unique selected call call').1
    | load place loaded => cases place
  | callTerminated args call =>
    cases second with
    | expression ev' =>
      cases ev' with
      | call args' call' =>
        obtain ⟨rfl,rfl,rfl⟩:=ApplicationPureCall.args_unique closed args args'
        cases (CanonicalSource.call_unique selected call call').1
      | load place loaded => cases place
    | callTerminated args' call' =>
      obtain ⟨rfl,rfl,rfl⟩:=ApplicationPureCall.args_unique closed args args'
      obtain ⟨eq,state⟩:=CanonicalSource.call_unique selected call call'
      cases eq
      exact ⟨rfl,state.symm⟩

private theorem consume_prefix {F : Type} {context : Context F} {before middle after : State F}
    {xs ys : List Stmt} {flow : Flow} (known : ExecList context before xs .normal middle)
    (unique : ∀s∈xs,CompareSource.Unique context s)
    (actual : ExecList context before (xs++ys) flow after) : ExecList context middle ys flow after := by
  induction xs generalizing before with
  | nil => cases known;exact actual
  | cons x xs ih =>
    cases known with
    | cons head tail =>
      have hu : CompareSource.Unique context x :=unique x (by simp)
      have tu : ∀s∈xs,CompareSource.Unique context s:=fun s hs => unique s (by simp [hs])
      cases actual with
      | cons head' tail' =>
        obtain ⟨_,eq⟩:=hu head head'
        cases eq
        exact ih tail tu tail'
      | abrupt head' ne => exact False.elim (ne (hu head head').1.symm)
    | abrupt run ne => exact False.elim (ne rfl)

private theorem append_exec {F : Type} {context : Context F} {before middle after : State F}
    {xs ys : List Stmt} {flow : Flow} (first : ExecList context before xs .normal middle)
    (second : ExecList context middle ys flow after) : ExecList context before (xs++ys) flow after := by
  induction xs generalizing before with
  | nil => cases first;exact second
  | cons x xs ih =>
    cases first with
    | cons run rest => exact .cons run (ih rest)
    | abrupt run ne => exact False.elim (ne rfl)

private theorem prefix_unique {F : Type} (context : Context F) :
    ∀s∈[signDeclaration,signBranch,lostDeclaration,resetIndex,lostLoop,resetIndex,copyLoop,signStore,overflowDeclaration],
      CompareSource.Unique context s := by
  intro s member
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at member
  rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first
    | exact sign_branch_unique context
    | exact lost_loop_unique context
    | exact copy_loop_unique context
    | (intro before a b fa fb first second
       exact PureDeterminism.simple_unique
         (by simp [signDeclaration,lostDeclaration,resetIndex,signStore,overflowDeclaration,v,lit,
           PureDeterminism.Simple,SourcePure.CallFree]) first second)

theorem suffix_total {F : Type} (context : Context F)
    (incSelected : findFunction context.program "increment_words"=some increment_words_ast)
    (canonSelected : findFunction context.program "canonical_sign"=some FFTRecursivePV.canonical_sign_ast)
    {before : State F}
    {outObj outSize outStart aObj aSize aStart bObj bSize bStart workObj workSize workStart : Nat}
    {ids owners : PVar → Nat} {old aData bData data : Nat → Nat}
    (locals : Bindings before pName pType ids owners (pValue outObj outStart aObj aStart bObj bStart workObj workStart 5))
    (well : WellScoped before) (outRep : WordArrayRep before outObj outSize old)
    (aRep : WordArrayRep before aObj aSize aData) (bRep : WordArrayRep before bObj bSize bData)
    (workRep : WordArrayRep before workObj workSize data)
    (separate : ∀v,outObj≠ids v ∧ workObj≠ids v)
    (shape : workObj=outObj → workSize=outSize)
    (disjoint : outObj≠workObj ∨ outStart+6≤workStart ∨ workStart+10≤outStart)
    (outBound : outStart+6≤outSize) (aBound : aStart+6≤aSize) (bBound : bStart+6≤bSize)
    (workBound : workStart+10≤workSize) (digits : ∀k,k<10 → data (workStart+k)<1000000000) :
    let sign:=signBit (aData (aStart+5)) (bData (bStart+5))
    ∃after,ExecList context before statements
        (.returned (.integer (integer64 (finalStatus old data outStart workStart sign)))) after ∧
      WordArrayRep after outObj outSize (finalData old data outStart workStart sign) ∧
      ∀after' flow,ExecList context before statements flow after' →
        flow=.returned (.integer (integer64 (finalStatus old data outStart workStart sign))) ∧ after'=after := by
  dsimp only
  let sign:=signBit (aData (aStart+5)) (bData (bStart+5))
  obtain ⟨s0,lostId,prepareRun,h0⟩:=prepare_execution context locals well outRep aRep bRep workRep
    separate shape disjoint outBound aBound bBound workBound digits
  let mids:=preparedIds ids before.nextObject lostId
  let midOwners:=preparedOwners owners before.scope before.scope
  obtain ⟨s1,middleRun,h1,l1⟩:=middle_execution context h0
  have sb : sign≤1:=by unfold sign signBit;split <;> omega
  obtain ⟨s2,signRun,h2⟩:=sign_store_execution context h1 l1 h0.separate (fun k hk => digits k hk) sb
  obtain ⟨s3,overflowRun,h3,fullLocals⟩:=overflow_declaration_execution context h2
  let fullIds:=extend mids s2.nextObject
  let fullOwners:=extend midOwners s2.scope
  have fullOutputLocals : Bindings s3 tailName tailType fullIds fullOwners
      (tailValues outObj outStart workObj workStart sign (CanonicalSource.digitSum data workStart 4) (data (workStart+9))) := by
    exact fullLocals
  have rawDigit : data (workStart+9)<1000000000:=digits 9 (by omega)
  obtain ⟨current,wr,vals⟩:=h2.work
  have oldOut:=h2.well.objectIds _ _ h2.output.2.1
  have oldWork:=h2.well.objectIds _ _ wr.2.1
  have hr : RoundView s3 outObj outSize outStart workObj workSize workStart fullIds fullOwners
      (retainedData old data outStart workStart sign) (fun k => data (workStart+k)) sign
      (CanonicalSource.digitSum data workStart 4) (data (workStart+9)) := by
    refine ⟨h3.output,h3.work,fullOutputLocals,?_,h3.shape,h3.disjoint,h3.outBound,h3.workBound,?_,sb,?_,rawDigit.le,h3.well⟩
    · intro v
      cases v with
      | inl v => exact h3.separate v
      | inr v => exact ⟨by change outObj≠s2.nextObject;omega,by change workObj≠s2.nextObject;omega⟩
    · intro i hi
      rw [retainedData_digit old data outStart workStart sign i hi]
      exact digits (i+4) (by omega)
    · exact CanonicalSource.digitSum_fits data workStart 4 (by omega) (fun i hi => digits i (by omega))
  obtain ⟨s4,roundRun,h4⟩:=rounding_execution context incSelected hr rawDigit
  obtain ⟨after,finishRun,finalRep,signedEq,frame⟩:=finish_execution context canonSelected h4
  have first := append_exec prepareRun middleRun
  have second : ExecList context s1 [signStore,overflowDeclaration,roundingBranch,canonicalCall,returnOverflow]
      (.returned (.integer (integer64 (finalStatus old data outStart workStart sign)))) after :=
    .cons signRun (.cons overflowRun (.cons roundRun finishRun))
  have whole : ExecList context before statements
      (.returned (.integer (integer64 (finalStatus old data outStart workStart sign)))) after := by
    simpa only [statements,List.append_assoc,List.cons_append,List.nil_append] using append_exec first second
  refine ⟨after,whole,finalRep,?_⟩
  intro after' flow actual
  have prefixRun:=append_exec first (.cons signRun (.cons overflowRun .nil))
  have remaining : ExecList context s3 [roundingBranch,canonicalCall,returnOverflow] flow after' :=
    consume_prefix prefixRun (prefix_unique context) (by simpa only [statements,List.append_assoc,List.cons_append,List.nil_append] using actual)
  have finishUnique : ∀s∈[canonicalCall,returnOverflow],CompareSource.Unique context s := by
    intro s member
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at member
    rcases member with rfl|rfl
    · exact canonical_expression_unique canonSelected
    · intro before a b fa fb first second
      exact PureDeterminism.simple_unique (by simp [returnOverflow,v,PureDeterminism.Simple,SourcePure.CallFree]) first second
  cases remaining with
  | cons actualRound actualFinish =>
    obtain ⟨_,stateEq⟩:=rounding_unique_at context incSelected hr roundRun actualRound
    cases stateEq
    exact CompareSource.list_unique finishUnique actualFinish finishRun
  | abrupt actualRound nonnormal =>
    exact False.elim (nonnormal (rounding_unique_at context incSelected hr roundRun actualRound).1.symm)

#print axioms suffix_total
end RH080Next.FFTPV.MultiplySuffix
