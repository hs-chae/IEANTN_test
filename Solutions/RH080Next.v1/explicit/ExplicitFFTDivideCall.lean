/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTDivideTail
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.DivideSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings
open FFT.Limbs
open IncrementSource (base)

def jDeclaration : Stmt:=.declare .u64 "j" (some (.variable "n"))
def remDeclaration : Stmt:=.declare .u64 "rem" (some (.literal (.integer 0 "ULL")))
def returnStatement : Stmt:=.returnValue (some (.literal (.integer 0 "ULL")))
def functionStatements : List Stmt:=[jDeclaration,remDeclaration,loop,roundingStatement,returnStatement]

theorem actual_body : divide_small_ast.body=.block functionStatements:=by rfl

/-- Complete application-source division call, including both optional
rounding branches and the verified nested increment call. -/
theorem divide_small_call {F : Type} (context : Context F)
    (selected : findFunction context.program "divide_small"=some divide_small_ast)
    (incrementSelected : findFunction context.program "increment_words"=some increment_words_ast)
    (before : State F) (object length start n d ceiling : Nat) (old : Nat → Nat)
    (well : WellScoped before) (rep : WordArrayRep before object length old)
    (bound : start+n ≤ length) (small : n ≤ 6) (digits : ∀i < n,old (start+i) < base)
    (hd : 0 < d) (hdb : d < base) (hceil : ceiling ≤ 1) :
    ∃after,Call context "divide_small" [.pointer (wordPointer object start),.integer (integer64 n),
        .integer (integer64 d),.integer (integer64 ceiling)] before (.value (.integer (integer64 0))) after ∧
      WordArrayRep after object length (roundedData old start n d ceiling) ∧
      IncrementSource.FullCallerFrame before after object := by
  let entry : State F:={before.enterScope with environment:=[]}
  have we : WellScoped entry:=wellScoped_environment (wellScoped_enter well) []
  obtain ⟨sa,sn,sd,sce,sj,sr,da,dn,dd,dce,dj,dr,view⟩:=
    initialize_parameters we rfl rep bound small digits hd hdb hceil
  obtain ⟨middle,loopRun,post,loopFrame⟩:=loop_execution context n view
  obtain ⟨last,roundRun,roundRep,roundFrame⟩:=rounding_execution context incrementSelected post
  have params : bindParameters entry divide_small_ast.parameters
      [.pointer (wordPointer object start),.integer (integer64 n),.integer (integer64 d),.integer (integer64 ceiling)]=some sce := by
    change bindParameters entry [(.pointer .u64,"a"),(.u64,"n"),(.u64,"d"),(.u64,"ceiling")]
      [.pointer (wordPointer object start),.integer (integer64 n),.integer (integer64 d),.integer (integer64 ceiling)]=some sce
    simp [bindParameters,da,dn,dd,dce]
  have wa:=wellScoped_declare we da
  have wn:=wellScoped_declare wa dn
  have wd:=wellScoped_declare wn dd
  have inn:=declare_storable (ZeroFrame.u64_storable n (by omega)) (convert64 n (by omega)) dn
  have idd:=declare_storable (ZeroFrame.u64_storable d (by dsimp [base] at hdb; omega)) (convert64 d (by dsimp [base] at hdb; omega)) dd
  have ice:=declare_storable (ZeroFrame.u64_storable ceiling (by omega)) (convert64 ceiling (by omega)) dce
  have nSlot:=ApplicationBirthFrame.slot_declare_old wd (ApplicationBirthFrame.slot_declare_old wn inn.slot idd) ice
  have nName : sce.environment.lookup "n"=some (scalarPointer sa.nextObject .u64) := by
    simp [ice.environment,idd.environment,inn.environment,List.lookup]
  have jRun : Exec context sce jDeclaration .normal sj:=.declareSome (.variable nName nSlot.read) dj
  have remRun : Exec context sj remDeclaration .normal sr:=
    .declareSome (.literal (.integer 0 "ULL") _ (.integer (integer64 0)) (by rfl)) dr
  have bodyRun : ExecList context sce functionStatements (.returned (.integer (integer64 0))) last := by
    by_cases positive : 0 < ceiling ∧ 0 < (division old start n d 0).2
    · exact .cons jRun (.cons remRun (.cons loopRun
        (.abrupt (by simpa only [roundingFlow,if_pos positive] using roundRun) (by simp))))
    · exact .cons jRun (.cons remRun (.cons loopRun
        (.cons (by simpa only [roundingFlow,if_neg positive] using roundRun)
          (.abrupt (.returnSome (.literal (.integer 0 "ULL") _ (.integer (integer64 0)) (by rfl))) (by simp)))))
  let after : State F:={last.leaveScope entry.scope before.environment with scope:=before.scope}
  have paramChain : Declarations entry sce:=.cons da (.cons dn (.cons dd (.cons dce (.nil sce))))
  have chain : Declarations entry sr:=.cons da (.cons dn (.cons dd (.cons dce (.cons dj (.cons dr (.nil sr))))))
  have fields:=chain.fields
  have called : Call context "divide_small"
      [.pointer (wordPointer object start),.integer (integer64 n),.integer (integer64 d),.integer (integer64 ceiling)] before
      (.value (.integer (integer64 0))) after := by
    apply Call.internal (function:=divide_small_ast) (entered:=sce) (middle:=last) selected actual_body params
    · exact Body.finish bodyRun (by intro label he; cases he)
    · exact convert64 0 (by norm_num)
    · simp only [after,paramChain.fields.2.1]
  have oldObjects : ∀id,id < before.nextObject → id≠object → after.objects id=before.objects id := by
    intro id old different
    have oldEntry : id < entry.nextObject:=old
    have oldSr : id < sr.nextObject:=lt_of_lt_of_le oldEntry fields.1
    have oldMiddle : id < middle.nextObject:=lt_of_lt_of_le oldSr loopFrame.nextObject
    have absent : id∉writes object (ids entry.nextObject) := by
      have nj : id≠ids entry.nextObject Var.j:=by change id≠before.nextObject+4; omega
      have nr : id≠ids entry.nextObject Var.rem:=by change id≠before.nextObject+5; omega
      simp [writes,different,nj,nr]
    have same : last.objects id=before.objects id:=
      (roundFrame.objects id oldMiddle different).trans
        ((loopFrame.outside id oldSr absent).trans (fields.2.2.2.2 id oldEntry))
    change (last.objects id).map _=before.objects id
    rw [same]
    cases present : before.objects id with
    | none=>rfl
    | some obj=>
      have storage : obj.storage≠.automatic entry.scope := by
        intro bad
        have hb:=well.automatic id obj before.nextScope present bad
        omega
      simp [storage]
  have scopes : before.nextScope ≤ last.nextScope := by
    have ns:=fields.2.2.1
    have m1:=loopFrame.nextScope
    have m2:=roundFrame.nextScope
    change sr.nextScope=before.nextScope+1 at ns
    omega
  have afterWell : WellScoped after := by
    apply wellScoped_scope (wellScoped_leave roundFrame.well entry.scope before.environment)
    have current:=well.current
    change before.scope < last.nextScope
    omega
  have declForeign : sr.foreign=entry.foreign:=
    (declare_foreign dr).trans ((declare_foreign dj).trans ((declare_foreign dce).trans
      ((declare_foreign dd).trans ((declare_foreign dn).trans (declare_foreign da)))))
  have foreign : after.foreign=before.foreign := by
    change last.foreign=entry.foreign
    exact roundFrame.foreign.trans (loopFrame.foreign.trans declForeign)
  refine ⟨after,called,IncrementSource.wordArray_leave roundRep,
    ⟨rfl,rfl,foreign,afterWell,oldObjects⟩,fields.1.trans (loopFrame.nextObject.trans roundFrame.nextObject),scopes,?_⟩
  exact roundFrame.mode.trans (loopFrame.mode.trans fields.2.2.2.1)

#print axioms divide_small_call
end RH080Next.FFTPV.DivideSource
