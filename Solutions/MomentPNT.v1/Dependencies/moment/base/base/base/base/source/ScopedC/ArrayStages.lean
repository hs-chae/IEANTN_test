/- Copyright (c) 2026 IEANTN contributors. Apache-2.0. -/
import ScopedC.ArraySourceExecute
import ScopedC.StateWordEquality

namespace ScopedC.ArrayStages
open ScopedC.Syntax ScopedC.Machine ScopedC.ArraySourceCalls
set_option autoImplicit false
set_option maxHeartbeats 0

/-- Full application memory with the actual runtime arena carried explicitly.
The cache never decides equality of the arena's owner function. -/
def withArena (shape : State) (arena : NatArena.Arena) : State :=
  {shape with nats:=arena}

def hasNext (result : Option ArraySourceExecute.Outcome) (shape : State) : Bool :=
  match result with
  | some (.continuing t) => StateWordEquality.stateEq 16 t shape
  | _ => false

theorem hasNext_sound {result : Option ArraySourceExecute.Outcome} {shape : State}
    (h : hasNext result shape = true) :
    ∃ arena, result = some (.continuing (withArena shape arena)) := by
  cases result with
  | none => simp [hasNext] at h
  | some out =>
    cases out with
    | returned t v => simp [hasNext] at h
    | continuing t =>
      have he : t = withArena shape t.nats := StateWordEquality.stateEq_sound h
      exact ⟨t.nats,he ▸ rfl⟩

/-- A genuine execution of one actual statement for every carried arena.
Both the statement execution and all application memory are verified. There
is no unverified state transition or expected mathematical output premise.
Quantification permits later statements to use the actual returned arena,
without a guessed unchanged-arena assertion. -/
def ShapeRun (cfg : Layout) (service : Call) (st : Stmt) (before after : State) : Prop :=
  ∀ arena, ∃ finalArena, Run cfg service st (withArena before arena)
    (.continuing (withArena after finalArena))

theorem statement_of_checked {cfg : Layout} {service : Call}
    {expressionFuel statementFuel : Nat} {st : Stmt} {before after : State}
    (h : ∀ arena, hasNext (ArraySourceExecute.statement cfg service expressionFuel statementFuel
      st (withArena before arena)) after = true) : ShapeRun cfg service st before after := by
  intro arena
  obtain ⟨finalArena,he⟩ := hasNext_sound (h arena)
  exact ⟨finalArena,ArraySourceExecute.statement_sound he⟩

/-- Every intermediate state must have its own accepted actual-statement
execution proof. Cache data alone cannot construct this proof. -/
inductive Chain (cfg : Layout) (service : Call) : List Stmt → State → State → Prop
  | nil (s : State) : Chain cfg service [] s s
  | next {head tail before middle after}
      (first : ShapeRun cfg service head before middle)
      (rest : Chain cfg service tail middle after) :
      Chain cfg service (head::tail) before after

theorem sequence_of_chain {cfg : Layout} {service : Call}
    {stmts : List Stmt} {before after : State}
    (chain : Chain cfg service stmts before after) :
    ∀ arena, ∃ finalArena,
      Loops.SeqRun (Eval cfg service) (Declare cfg service) truth Scope stmts
        (withArena before arena) (.continuing (withArena after finalArena)) := by
  induction chain with
  | nil s => intro arena; exact ⟨arena,Loops.SeqRun.nil _⟩
  | next first rest ih =>
    intro arena
    obtain ⟨middleArena,head⟩ := first arena
    obtain ⟨finalArena,tail⟩ := ih middleArena
    exact ⟨finalArena,Loops.SeqRun.next head tail⟩

/-- The scope exit is exactly the pre-existing stack-pop rule. Writes to
older objects, global state and the actual arena survive. -/
theorem sequence_statement_of_chain {cfg : Layout} {service : Call}
    {stmts : List Stmt} {before after : State}
    (chain : Chain cfg service stmts before after) (arena : NatArena.Arena) :
    ∃ finalArena, Run cfg service (.sequence stmts) (withArena before arena)
      (.continuing (popScope (withArena before arena) (withArena after finalArena))) := by
  obtain ⟨finalArena,body⟩ := sequence_of_chain chain arena
  exact ⟨finalArena,Loops.StmtRun.sequence body rfl⟩

end ScopedC.ArrayStages
