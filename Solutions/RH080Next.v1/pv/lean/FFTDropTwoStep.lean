/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTDropTwoBase
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.DropTwoSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings

/-- The actual overlapping forward move reads the original, still-unread
higher limb before storing the lower one. Aliasing is explicitly supported. -/
theorem move_execution {F : Type} (context : Context F) {before : State F}
    {workObject owner i : Nat} {ids : Var→Nat} {old : Nat→Nat}
    (h : View before workObject ids owner i old) (inside : i<4) :
    ∃middle,Exec context before move .normal middle ∧
      WordArrayRep middle workObject 512 (shifted old 192 (i+1)) ∧
      Locals middle name type ids owner (values workObject old i) ∧
      WellScoped middle ∧ ScanFrame.Frame before middle [workObject,ids Var.i] := by
  have digit:=h.digits (i+2) (by omega)
  have fits : old (192+i+2)<2^64:=by dsimp [base] at digit;simp only [Nat.add_assoc] at digit ⊢;omega
  obtain ⟨middle,written,rep⟩:=word_store_with_rep h.array (show 192+i<512 by omega) fits
  have run : Exec context before move .normal middle:=by
    apply Exec.assign (value:=.integer (integer64 (old (192+i+2)))) (source_eval context h inside)
      (.index (.variable (h.locals.lookup Var.total) (h.locals.read Var.total))
        (.variable (h.locals.lookup Var.i) (h.locals.read Var.i)) (slice_pointer_add h.array (show 192+i<512 by omega)))
    exact written
  have params:=ApplicationBirthFrame.locals_store_other h.locals (fun v=>(h.separate v).symm) written
  exact ⟨middle,run,rep,params,wellScoped_store h.well written,ScanFrame.Frame.store (by simp [wordPointer]) written⟩

theorem step_execution {F : Type} (context : Context F) {before : State F}
    {workObject owner i : Nat} {ids : Var→Nat} {old : Nat→Nat}
    (h : View before workObject ids owner i old) (inside : i<4) :
    ∃after,Exec context before loopBody .normal after ∧ View after workObject ids owner (i+1) old ∧
      ScanFrame.Frame before after [workObject,ids Var.i] := by
  obtain ⟨middle,moveRun,array,params,wm,moveFrame⟩:=move_execution context h.enter inside
  have nextFits : i+1<2^64:=by omega
  obtain ⟨last,written⟩:=ProductInner.slot_store_exists (params.slots Var.i) (.integer (integer64 (i+1))) (ZeroFrame.u64_storable _ nextFits)
  have inc : Exec context middle advance .normal last := by
    apply Exec.assign (value:=.integer (integer64 (i+1)))
      (Eval.paren (Eval.binaryLR (.variable (params.lookup Var.i) (params.read Var.i))
        (.literal (.integer 1 "ULL") _ (.integer (integer64 1)) (by rfl))
        (by simp only [values,binary,binary64_add i 1 (by omega) (by norm_num) nextFits,Option.map_some])))
      (.variable (params.lookup Var.i))
    exact written
  have nextLocals:=params.store Var.i (.integer (integer64 (i+1))) (ZeroFrame.u64_storable _ nextFits) written
  have valuesEq : Function.update (values workObject old i) Var.i (.integer (integer64 (i+1)))=values workObject old (i+1):=by
    funext v;cases v <;> simp [values,Function.update]
  rw [valuesEq] at nextLocals
  have storeFields:=SourceLocals.store_frame written
  have nextArray : WordArrayRep last workObject 512 (shifted old 192 (i+1)) :=
    ⟨storeFields.2.1.trans array.1,(storeFields.2.2.2.2.2 workObject (h.separate Var.i)).trans array.2.1,array.2.2⟩
  have lastFrame : ScanFrame.Frame middle last [workObject,ids Var.i]:=ScanFrame.Frame.store (by simp [scalarPointer]) written
  let after : State F:={last.leaveScope before.nextScope before.environment with scope:=before.scope}
  have runList : ExecList context before.enterScope [move,advance] .normal last:=.cons moveRun (.cons inc .nil)
  have run : Exec context before loopBody .normal after:=.block (by rfl) runList (by rfl)
  have only : SourceNoAlloc.Only loopBody:=by simp [loopBody,move,sourceIndex,advance,SourceNoAlloc.Only,SourcePure.CallFree]
  have effect:=SourceNoAlloc.exec_effect run only h.well
  have post : View after workObject ids owner (i+1) old:=
    ⟨nextLocals.leave (by have b:=h.locals.bound;omega) before.environment h.locals.lookup before.scope,
      ComplexSource.word_array_leave nextArray before.nextScope before.scope before.environment,
      h.separate,h.digits,by omega,effect.well⟩
  exact ⟨after,run,post,ScanFrame.Frame.close h.well (moveFrame.trans lastFrame)⟩

#print axioms move_execution
#print axioms step_execution
end RH080Next.FFTPV.DropTwoSource
