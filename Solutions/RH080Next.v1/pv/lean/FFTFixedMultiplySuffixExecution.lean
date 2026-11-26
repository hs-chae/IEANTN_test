/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTFixedMultiplySuffixPrepare
import FFTFixedMultiplySuffixFinish
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.MultiplySuffix
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots ProductInner

def retainedData (old data : Nat → Nat) (outStart workStart sign : Nat) : Nat → Nat :=
  Function.update (copied old (fun k => data (workStart+k)) outStart 5) (outStart+5) sign

def finalData (old data : Nat → Nat) (outStart workStart sign : Nat) : Nat → Nat :=
  CanonicalSource.canonicalData (roundedData (retainedData old data outStart workStart sign)
    outStart sign (CanonicalSource.digitSum data workStart 4)) outStart

def finalStatus (old data : Nat → Nat) (outStart workStart sign : Nat) : Nat :=
  data (workStart+9)+roundingCarry (retainedData old data outStart workStart sign)
    outStart sign (CanonicalSource.digitSum data workStart 4)

private theorem append_exec {F : Type} {context : Context F} {before middle after : State F}
    {xs ys : List Stmt} {flow : Flow} (first : ExecList context before xs .normal middle)
    (second : ExecList context middle ys flow after) : ExecList context before (xs++ys) flow after := by
  induction xs generalizing before with
  | nil => cases first;exact second
  | cons x xs ih =>
    cases first with
    | cons run rest => exact .cons run (ih rest)
    | abrupt run ne => exact False.elim (ne rfl)

theorem retainedData_digit (old data : Nat → Nat) (outStart workStart sign i : Nat) (hi : i<5) :
    retainedData old data outStart workStart sign (outStart+i)=data (workStart+(i+4)) := by
  rw [retainedData,Function.update_of_ne (by omega)]
  simp [copied,CopyLoop.prefixData,show outStart≤outStart+i ∧ outStart+i<outStart+5 by omega]

/-- Every instruction of the actual multiplication suffix executes, including
real local births, both loops, optional increment and canonical-sign Call.
The output and status are computed from actual ten-word product data. -/
theorem suffix_execution {F : Type} (context : Context F)
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
      WordArrayRep after outObj outSize (finalData old data outStart workStart sign) := by
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
  refine ⟨after,?_,finalRep⟩
  simpa only [statements,List.append_assoc,List.cons_append,List.nil_append] using append_exec first second

#print axioms retainedData_digit
#print axioms suffix_execution
end RH080Next.FFTPV.MultiplySuffix
