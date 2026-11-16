/- Copyright (c) 2026 IEANTN contributors. Apache-2.0. -/
import ScopedC.ArraySourceCallExecute
import ScopedC.ArrayCallCheck
import SynergyHeightC.BoundInitialization
import SynergyHeightC.InitCacheProposal

namespace SynergyHeightC.InitExecute
open ScopedC ScopedC.Syntax ScopedC.Machine ScopedC.ArraySourceCalls
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Execute the actual source function from the source-derived fourteen
static globals. Every application callee is another actual installed body.
No constant-cache word is supplied to the executor or its call service. -/
@[irreducible] def run : Option (Value × State) :=
  ArraySourceCallExecute.execute SynergyC.Header.layout Generated.functions 128 2048 16
    "initializePointConstants" [] Initialization.state

/-- This equality check follows actual source execution. It is not a mere
certificate check: the complete source AST executes before the proposed
state is examined. All heap objects and both environments must agree. The
actual returned Nat arena is preserved, not guessed or equated to a function.
-/
def checked : Bool :=
  ArrayCallCheck.hasState run (InitCacheProposal.postState NatArena.empty)

theorem source_of_checked (h : checked = true) :
    ∃ arena, SourceCall SynergyC.Header.layout Generated.functions 16 "initializePointConstants" []
      Initialization.state .unit (InitCacheProposal.postState arena) := by
  unfold checked at h
  have run_eq : run = ArraySourceCallExecute.execute SynergyC.Header.layout
      Generated.functions 128 2048 16 "initializePointConstants" [] Initialization.state := by
    unfold run
    rfl
  have hc := Eq.mp (congrArg (fun result => ArrayCallCheck.hasState result
      (InitCacheProposal.postState NatArena.empty) = true) run_eq) h
  obtain ⟨t,hs,he⟩ := ArrayCallCheck.source_of_checked hc
  have eqt : t = InitCacheProposal.postState t.nats := he
  exact ⟨t.nats,eqt ▸ hs⟩

/-- Bind the checked execution back to the actual physical source tree. -/
theorem bound_source_of_checked (h : checked = true) :
    ∃ arena, SourceCall SynergyC.Header.layout Bundle.code 16 "initializePointConstants" []
      Initialization.state .unit (InitCacheProposal.postState arena) := by
  exact Eq.mpr (congrArg (fun code => ∃ arena,
    SourceCall SynergyC.Header.layout code 16 "initializePointConstants" []
      Initialization.state .unit (InitCacheProposal.postState arena)) Bundle.code_exact)
    (source_of_checked h)

#print axioms source_of_checked
#print axioms bound_source_of_checked
end SynergyHeightC.InitExecute
