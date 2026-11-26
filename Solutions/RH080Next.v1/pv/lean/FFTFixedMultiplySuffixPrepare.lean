/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTFixedMultiplySuffixSign
import FFTFixedMultiplySuffixMiddle
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.MultiplySuffix
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots ProductInner

def midEmbed : MVar → Sum (Sum PVar Unit) Unit
  | .out => .inl (.inl .out) | .work => .inl (.inl .work) | .i => .inl (.inl .i)
  | .sign => .inl (.inr ()) | .lost => .inr ()
private theorem midEmbed_injective : Function.Injective midEmbed := by
  intro a b eq;cases a <;> cases b <;> cases eq <;> rfl

def preparedIds (ids : PVar → Nat) (signId lostId : Nat) : MVar → Nat :=
  extend (extend ids signId) lostId ∘ midEmbed
def preparedOwners (owners : PVar → Nat) (signOwner lostOwner : Nat) : MVar → Nat :=
  extend (extend owners signOwner) lostOwner ∘ midEmbed

private theorem append_normal {F : Type} {context : Context F} {before middle after : State F}
    {xs ys : List Stmt} (first : ExecList context before xs .normal middle)
    (second : ExecList context middle ys .normal after) : ExecList context before (xs++ys) .normal after := by
  induction xs generalizing before with
  | nil => cases first;exact second
  | cons x xs ih =>
    cases first with
    | cons run rest => exact .cons run (ih rest)
    | abrupt run ne => exact False.elim (ne rfl)

/-- The suffix initializes sign/lost by the real source declarations and resets
i through its actual typed slot. Its loop precondition is constructed rather
than postulated as an application initialization fact. -/
theorem prepare_execution {F : Type} (context : Context F) {before : State F}
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
    ∃after lostId,ExecList context before [signDeclaration,signBranch,lostDeclaration,resetIndex] .normal after ∧
      MiddleView after outObj outSize outStart workObj workSize workStart
        (preparedIds ids before.nextObject lostId) (preparedOwners owners before.scope before.scope)
        old data 0 (signBit (aData (aStart+5)) (bData (bStart+5))) 0 := by
  obtain ⟨signed,signRun,signLocals,signWell,signOld,signNo,signScope,signMode⟩:=sign_execution context locals well aRep bRep aBound bBound
  have outOld:=well.objectIds _ _ outRep.2.1
  have workOld:=well.objectIds _ _ workRep.2.1
  have or1 : WordArrayRep signed outObj outSize old :=
    ⟨signMode.trans outRep.1,(signOld outObj outOld).trans outRep.2.1,outRep.2.2⟩
  have wr1 : WordArrayRep signed workObj workSize data :=
    ⟨or1.1,(signOld workObj workOld).trans workRep.2.1,workRep.2.2⟩
  have storage:=ZeroFrame.u64_storable 0 (by norm_num)
  obtain ⟨declared,decl⟩:=ZeroFrame.declare_exists signWell .u64 "lost" _ storage
  have d:=declare_storable storage storage.converted decl
  have wd:=wellScoped_declare signWell decl
  have hd:=bindings_extend_declaration signLocals signWell
    (by intro x;cases x with
        | inl x => cases x <;> decide
        | inr x => cases x;decide) d
  have projection:=bindings_reindex hd midEmbed midEmbed_injective
  have names : extend (extend pName "sign") "lost" ∘ midEmbed = midName := by funext x;cases x <;> rfl
  have types : extend (extend pType .u64) .u64 ∘ midEmbed = midType := by funext x;cases x <;> rfl
  have values : extend (extend (pValue outObj outStart aObj aStart bObj bStart workObj workStart 5)
      (.integer (integer64 (signBit (aData (aStart+5)) (bData (bStart+5)))))) (.integer (integer64 0)) ∘ midEmbed =
      midValues outObj outStart workObj workStart 5 (signBit (aData (aStart+5)) (bData (bStart+5))) 0 := by
    funext x;cases x <;> rfl
  rw [names,types,values] at projection
  have freshOut : outObj≠signed.nextObject := by rw [signNo];omega
  have freshWork : workObj≠signed.nextObject := by rw [signNo];omega
  have or2 : WordArrayRep declared outObj outSize old :=
    ⟨d.mode.trans or1.1,(d.outside outObj freshOut).trans or1.2.1,or1.2.2⟩
  have wr2 : WordArrayRep declared workObj workSize data :=
    ⟨d.mode.trans wr1.1,(d.outside workObj freshWork).trans wr1.2.1,wr1.2.2⟩
  have hv : MiddleView declared outObj outSize outStart workObj workSize workStart
      (preparedIds ids before.nextObject signed.nextObject) (preparedOwners owners before.scope before.scope)
      old data 5 (signBit (aData (aStart+5)) (bData (bStart+5))) 0 := by
    refine ⟨or2,wr2,?_,?_,shape,disjoint,outBound,workBound,digits,wd⟩
    · simpa only [preparedIds,preparedOwners,signScope] using projection
    · intro x
      cases x <;> simp only [preparedIds,midEmbed,extend,Function.comp_apply,Sum.elim_inl,Sum.elim_inr]
      · exact separate PVar.out
      · exact separate PVar.work
      · exact separate PVar.i
      · constructor <;> omega
      · exact ⟨freshOut,freshWork⟩
  obtain ⟨after,resetRun,ha⟩:=reset_execution context hv
  have dr : Exec context signed lostDeclaration .normal declared :=
    .declareSome (.literal (.integer 0 "ULL") _ (.integer (integer64 0)) (by rfl)) decl
  have combined : ExecList context before [signDeclaration,signBranch,lostDeclaration,resetIndex] .normal after :=
    append_normal signRun (.cons dr (.cons resetRun .nil))
  exact ⟨after,signed.nextObject,combined,ha⟩

#print axioms prepare_execution
end RH080Next.FFTPV.MultiplySuffix
