/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTInputLoaderPrefix
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.InputLoader
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings
open RootSource

theorem PartialBindings.assign {F : Type} (context : Context F) {before : State F} {count fo bo cutoff : Nat}
    {ids : Var → Nat} {values : Var → Value} (h : PartialBindings before count fo bo ids values)
    (well : WellScoped before) (v : Var) (active : Active count v) (value : Value) (expression : Expr)
    (storable : Storable (varType v) value) (evaluated : Eval context before expression value before)
    (pure : SourcePure.CallFree expression) (writes : List Nat) (fresh : cutoff≤ before.nextObject)
    (permitted : ids v∈writes ∨ cutoff≤ ids v) :
    ∃after,Exec context before (.assign (.variable (varName v)) expression) .normal after ∧
      Every context before (.assign (.variable (varName v)) expression) .normal after ∧
      PartialBindings after count fo bo ids (Function.update values v value) ∧
      before.store (scalarPointer (ids v) (varType v)) value=some after ∧
      ApplicationBirthFrame.Frame cutoff before after writes:=by
  obtain ⟨after,stored⟩:=ProductInner.slot_store_exists (h.slots v active) value storable
  have run : Exec context before (.assign (.variable (varName v)) expression) .normal after:=
    .assign evaluated (.variable (h.lookup v active)) stored
  exact ⟨after,run,every_pure ⟨by trivial,pure⟩ run,h.store v active value storable stored,stored,
    ApplicationBirthFrame.store_frame cutoff writes well fresh permitted stored⟩

theorem PartialBindings.leave {F : Type} {state : State F} {count fo bo scope restore : Nat}
    {ids : Var → Nat} {values : Var → Value} (h : PartialBindings state count fo bo ids values)
    (different : ∀v,Active count v → scope≠owner fo bo v) (environment : List (String×Pointer))
    (lookup : ∀v,Active count v → environment.lookup (varName v)=some (scalarPointer (ids v) (varType v))) :
    PartialBindings {state.leaveScope scope environment with scope:=restore} count fo bo ids values:=by
  refine ⟨lookup,?_,h.distinct,h.bound⟩
  intro v hv
  refine ⟨(h.slots v hv).storable,?_⟩
  change (state.objects (ids v)).map _=_
  rw [(h.slots v hv).object]
  simp [scalarObject,(different v hv).symm]

theorem binary64_ge (a b : Nat) (ha : a<2^64) (hb : b<2^64) :
    Integer.binary .ge (integer64 a) (integer64 b)=some (.boolean (decide (b≤ a))):=by
  change some (Integer.boolean ((Integer.cast .u64 (b:Int)).toInt≤(Integer.cast .u64 (a:Int)).toInt))=_
  rw [cast64_exact a ha,cast64_exact b hb,integer64_toInt,integer64_toInt]
  congr 2
  simp

#print axioms PartialBindings.assign
#print axioms PartialBindings.leave
#print axioms binary64_ge
end RH080Next.FFTPV.InputLoader
