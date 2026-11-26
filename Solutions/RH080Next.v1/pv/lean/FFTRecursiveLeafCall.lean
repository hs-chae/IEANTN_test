/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTRecursiveLeafExpressions
import FFTRecursiveSourceLayout
import FFTRecursiveCopyFrame
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.RecursiveSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings ApplicationBirthFrame

private theorem declarations_foreign {F : Type} {before after : State F}
    (chain : Declarations before after) : after.foreign = before.foreign := by
  induction chain with
  | nil state => rfl
  | cons declared tail ih => exact ih.trans (declare_foreign declared)

/-- Closing actual automatic scopes preserves typed host arrays. -/
theorem word_array_leave {F : Type} {state : State F} {object size scope restore : Nat}
    {data : Nat → Nat} (rep : WordArrayRep state object size data)
    (environment : List (String × Pointer)) :
    WordArrayRep {state.leaveScope scope environment with scope := restore} object size data := by
  refine ⟨rep.1,?_,rep.2.2⟩
  change (state.objects object).map _ = some _
  rw [rep.2.1]
  simp [wordObject]

/-- Actual complete recursive C base-case Call. It really binds all nine
source parameters, tests n=1, enters the real branch block, calls the verified
copy_words source, returns and closes both scopes. No initialized callee state
or prescribed numerical output is assumed. -/
theorem leaf_call {F : Type} (context : Context F)
    (selected : findFunction context.program "fft_recursive" = some FFTRecursivePV.fft_recursive_ast)
    (copySelected : findFunction context.program "copy_words" = some FFTRecursivePV.copy_words_ast)
    (caller : State F) (outObj outSize inObj inSize twiddleObj workObj start index step total : Nat)
    (old input : Nat → Nat) (well : WellScoped caller)
    (output : WordArrayRep caller outObj outSize old)
    (inputRep : WordArrayRep caller inObj inSize input) (different : outObj ≠ inObj)
    (shape : IndexShape start index step 1 total)
    (outBound : 12*total ≤ outSize) (inBound : 12*total ≤ inSize) :
    ∃after, Call context "fft_recursive"
        (arguments outObj inObj twiddleObj workObj start index step 1 total)
        caller (.value (.integer (integer64 0))) after ∧
      WordArrayRep after outObj outSize
        (CopyLoop.prefixData old (fun j => input (index*12+j)) (start*12) 12) ∧
      WordArrayRep after inObj inSize input ∧
      Frame caller.nextObject caller after [outObj] := by
  let entry : State F := {caller.enterScope with environment := []}
  have we : WellScoped entry := wellScoped_environment (wellScoped_enter well) []
  have scalarBounds := shape.scalar_bounds
  obtain ⟨entered,bound,params,chain,pwell,pno,pscope,pns⟩ := initialize_parameters
    outObj inObj twiddleObj workObj start index step 1 total we rfl
    scalarBounds.1 scalarBounds.2.1 scalarBounds.2.2.1 (by norm_num) scalarBounds.2.2.2.2
  have fields := chain.fields
  have oc := well.objectIds _ _ output.2.1
  have ic := well.objectIds _ _ inputRep.2.1
  have outputP : WordArrayRep entered outObj outSize old :=
    ⟨fields.2.2.2.1.trans output.1,(fields.2.2.2.2 outObj oc).trans output.2.1,output.2.2⟩
  have inputP : WordArrayRep entered inObj inSize input :=
    ⟨fields.2.2.2.1.trans inputRep.1,(fields.2.2.2.2 inObj ic).trans inputRep.2.1,inputRep.2.2⟩
  have outRange : start*12+12 ≤ outSize := by have h := shape.output; omega
  have inRange : index*12+12 ≤ inSize := by
    have hi := shape.index
    have hp := shape.stride
    simp only [Nat.mul_one] at hp
    omega
  have offsetBounds := shape.source_offsets
  have outFit : start*12 < 2^64 := by omega
  have inFit : index*12 < 2^64 := by omega
  have paramsB := params.enter
  have outputB : WordArrayRep entered.enterScope outObj outSize old := outputP
  have inputB : WordArrayRep entered.enterScope inObj inSize input := inputP
  have args := leaf_arguments_eval context paramsB outputB inputB
    scalarBounds.1 scalarBounds.2.1 outFit inFit (by omega) (by omega)
  obtain ⟨copied,copyCall,copyOutput,copyRead,copyCaller,copyFrame⟩ :=
    CopyLoop.copy_words_call_framed context copySelected entered.enterScope
      outObj outSize (start*12) inObj inSize (index*12) 12 old input
      (wellScoped_enter pwell) outputB inputB
      (by intro same;exact False.elim (different same.symm))
      (Or.inl different) outRange inRange (by norm_num)
  have copiedStmt : Exec context entered.enterScope leafCopy .normal copied :=
    .expression (.call args copyCall)
  have zeroRun : Exec context copied zeroReturn (.returned (.integer (integer64 0))) copied :=
    .returnSome (.literal (.integer 0 "ULL") _ (.integer (integer64 0)) (by rfl))
  let branchAfter : State F :=
    {copied.leaveScope entered.nextScope entered.environment with scope := entered.scope}
  have blockRun : Exec context entered (.block [leafCopy,zeroReturn])
      (.returned (.integer (integer64 0))) branchAfter :=
    .block rfl (.cons copiedStmt (.abrupt zeroRun (by intro bad;cases bad))) rfl
  have test : Eval context entered leafCondition (.integer (.boolean true)) entered := by
    refine .binaryLR (Eval.variable (params.lookup .n) (params.read .n))
      (.literal (.integer 1 "ULL") _ (.integer (integer64 1)) (by rfl)) ?_
    rfl
  have branchRun : Exec context entered leafBranch (.returned (.integer (integer64 0))) branchAfter :=
    .ifTrue test (by rfl) blockRun
  have bodyRun : Body context functionStatements entered functionStatements
      (.returned (.integer (integer64 0))) branchAfter := by
    apply Body.finish
    · rw [actual_leaf_head]
      exact .abrupt branchRun (by intro bad;cases bad)
    · intro label bad
      cases bad
  let after : State F :=
    {branchAfter.leaveScope entered.scope caller.environment with scope := caller.scope}
  have called : Call context "fft_recursive"
      (arguments outObj inObj twiddleObj workObj start index step 1 total)
      caller (.value (.integer (integer64 0))) after :=
    .internal selected actual_body bound bodyRun (convert64 0 (by norm_num)) rfl
  have parameterFrame : Frame caller.nextObject caller.enterScope entered [outObj] := by
    refine ⟨pwell,fields.1,fields.1,?_,fields.2.2.2.1,
      (declarations_foreign chain).trans (show entry.foreign = caller.enterScope.foreign from rfl),?_⟩
    · rw [pns]
    · intro id old absent
      exact fields.2.2.2.2 id old
  have restrictedCopy : Frame caller.nextObject entered.enterScope copied [outObj] := by
    refine ⟨copyFrame.well,fields.1.trans copyFrame.fresh,copyFrame.nextObject,
      copyFrame.nextScope,copyFrame.mode,copyFrame.foreign,?_⟩
    intro id old absent
    exact copyFrame.outside id (old.trans_le fields.1) absent
  have branchFrame : Frame caller.nextObject entered branchAfter [outObj] :=
    close_frame pwell fields.1 restrictedCopy
  have finalFrame : Frame caller.nextObject caller after [outObj] := by
    have result := close_frame well (le_refl caller.nextObject) (parameterFrame.trans branchFrame)
    simpa only [after,pscope,entry,State.enterScope] using result
  have outputAfter : WordArrayRep after outObj outSize
      (CopyLoop.prefixData old (fun j => input (index*12+j)) (start*12) 12) :=
    word_array_leave (word_array_leave copyOutput entered.environment) caller.environment
  have inputAfter : WordArrayRep after inObj inSize input :=
    ⟨finalFrame.mode.trans inputRep.1,
      (finalFrame.outside inObj ic (by simpa [Ne.symm different])).trans inputRep.2.1,inputRep.2.2⟩
  exact ⟨after,called,outputAfter,inputAfter,finalFrame⟩

#print axioms leaf_call
end RH080Next.FFTPV.RecursiveSource
