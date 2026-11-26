/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTRecursiveLoopBindings
import ExplicitApplicationBirthFrame
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.RecursiveSource
open GoldbachDirect WordArrays SourceLocals SourceBindings SourceScalarSlots

/-- The actual source while-body block enters a fresh scope without changing
any persistent function binding or caller buffer. -/
theorem LoopView.enter {F : Type} {state : State F}
    {total : Nat} {buffers : Buffers total} {start index step n owner j : Nat}
    {ids : LoopVar → Nat} {input table output work : Nat → Nat}
    (h : LoopView state buffers start index step n ids owner j input table output work) :
    LoopView state.enterScope buffers start index step n ids owner j input table output work :=
  ⟨h.bindings.enter,h.arrays,wellScoped_enter h.well,h.active⟩

/-- An actual fresh source declaration preserves old typed loop variables and
all real buffers; new local initialization is never postulated. -/
theorem LoopView.declare {F : Type} {before after : State F}
    {total : Nat} {buffers : Buffers total} {start index step n owner j : Nat}
    {ids : LoopVar → Nat} {input table output work : Nat → Nat}
    {cname : String} {ctype : CType} {value : Value}
    (h : LoopView before buffers start index step n ids owner j input table output work)
    (different : ∀v, loopName v ≠ cname)
    (declared : Declaration before after cname ctype value)
    (actual : before.declare ctype cname (some value) = some after) :
    LoopView after buffers start index step n ids owner j input table output work :=
  ⟨h.bindings.declare h.well different declared,
    fun r => ApplicationBirthFrame.array_declare_old h.well (h.arrays r) declared,
    wellScoped_declare h.well actual,h.active⟩

end RH080Next.FFTPV.RecursiveSource
