/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTMultiplySmallSource
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.MultiplySmallSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings
open FFT.Limbs

/-- Counter and mode facts needed when this genuine application call is
composed inside another application function. No platform effect is assumed. -/
structure FullCallerFrame {F : Type} (before after : State F) (object : Nat)
    extends CallerFrame before after object : Prop where
  nextObject : before.nextObject ≤ after.nextObject
  nextScope : before.nextScope ≤ after.nextScope
  mode : after.mode=before.mode

theorem multiply_small_call_framed {F : Type} (context : Context F)
    (selected : findFunction context.program "multiply_small"=some multiply_small_ast)
    (before : State F) (object length start n factor : Nat) (old : Nat → Nat)
    (well : WellScoped before) (rep : WordArrayRep before object length old)
    (bound : start+n ≤ length) (small : n ≤ 6) (digits : ∀i < n,old (start+i) < base) (factorSmall : factor<base) :
    ∃after,Call context "multiply_small"
      [.pointer (wordPointer object start),.integer (integer64 n),.integer (integer64 factor)] before
      (.value (.integer (integer64 (scaledRow old start factor n).2))) after ∧
      WordArrayRep after object length (currentData old start factor n) ∧ FullCallerFrame before after object := by
  let entry : State F:={before.enterScope with environment:=[]}
  have we : WellScoped entry:=wellScoped_environment (wellScoped_enter well) []
  obtain ⟨sa,sn,sm,sj,sc,da,dn,dm,dj,dc,view⟩:=initialize_parameters we rfl rep bound small digits factorSmall
  obtain ⟨middle,loopRun,post,frame⟩:=loop_execution context n (j:=0) (n:=n) (by omega) view
  let carry:=(scaledRow old start factor n).2
  have hc : carry ≤ factor:=post.carry_bound
  have params : bindParameters entry multiply_small_ast.parameters
      [.pointer (wordPointer object start),.integer (integer64 n),.integer (integer64 factor)]=some sm := by
    change bindParameters entry [(.pointer .u64,"a"),(.u64,"n"),(.u64,"m")]
      [.pointer (wordPointer object start),.integer (integer64 n),.integer (integer64 factor)]=some sm
    simp [bindParameters,da,dn,dm]
  have bodyRun : ExecList context sm functionStatements (.returned (.integer (integer64 carry))) middle :=
    .cons (.declareSome (.literal (.integer 0 "ULL") _ (.integer (integer64 0)) (by rfl)) dj)
      (.cons (.declareSome (.literal (.integer 0 "ULL") _ (.integer (integer64 0)) (by rfl)) dc)
        (.cons loopRun (.abrupt (.returnSome (.variable (post.locals.lookup Var.carry)
          (post.locals.read Var.carry))) (by simp))))
  let after : State F:={middle.leaveScope entry.scope before.environment with scope:=before.scope}
  have smScope : sm.scope=entry.scope:=(declare_frame dm).1.trans ((declare_frame dn).1.trans (declare_frame da).1)
  have called : Call context "multiply_small"
      [.pointer (wordPointer object start),.integer (integer64 n),.integer (integer64 factor)] before
      (.value (.integer (integer64 carry))) after := by
    apply Call.internal (function:=multiply_small_ast) (entered:=sm) (middle:=middle)
      selected actual_body params
    · exact Body.finish bodyRun (by intro label he; cases he)
    · exact convert64 carry (by dsimp [base] at factorSmall;omega)
    · simp only [after,smScope]
  obtain ⟨known,original,knownRep,knownFrame⟩:=multiply_small_call context selected before object length start n factor old well rep bound small digits factorSmall
  have same:=(returned_call_unique selected original called).2
  cases same
  have chain : Declarations entry sc:=.cons da (.cons dn (.cons dm (.cons dj (.cons dc (.nil sc)))))
  have fields:=chain.fields
  refine ⟨after,called,knownRep,knownFrame,?_,?_,?_⟩
  · exact fields.1.trans frame.nextObject
  · have ns:=fields.2.2.1
    have mono:=frame.nextScope
    change sc.nextScope=before.nextScope+1 at ns
    change before.nextScope ≤ middle.nextScope
    omega
  · exact frame.mode.trans fields.2.2.2.1

#print axioms multiply_small_call_framed
end RH080Next.FFTPV.MultiplySmallSource
