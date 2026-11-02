import FKS2Scalar.HelperAudit

namespace FKS2SumBridge
open FKS2Scalar

structure Iteration where
  before : Frame
  afterBody : Frame
  afterIncrement : Frame
  eventsBefore : List HelperEvent
  eventsAfter : List HelperEvent
  deriving DecidableEq, Repr

structure LoopTrace where
  result : Frame
  events : List HelperEvent
  steps : List Iteration
  deriving DecidableEq, Repr

/-- Instrumentation calls the original body evaluator and records its state transitions.
Its control is a copy of evalLoop only; projection is proved below for every fuel/state. -/
def traceLoop : Nat → Frame → String → Rat → Bool → List Stmt → List HelperEvent → Option LoopTrace
  | 0, _, _, _, _, _, _ => none
  | n + 1, state, name, bound, inclusive, body, events => do
    if state.result.isSome then return ⟨state, events, []⟩
    let x ← get state.env name
    if (if inclusive then x ≤ bound else x < bound) then
      let (next, nextEvents) ← (evalBlock round64 selectedAST n state body).run events
      if next.result.isSome then
        return ⟨next, nextEvents, [⟨state, next, next, events, nextEvents⟩]⟩
      let old ← get next.env name
      let value ← round64 (old + 1)
      let advanced := { next with env := put next.env name value }
      let rest ← traceLoop n advanced name bound inclusive body nextEvents
      return { rest with steps := ⟨state, next, advanced, events, nextEvents⟩ :: rest.steps }
    else return ⟨state, events, []⟩

def project (t : LoopTrace) : Frame × List HelperEvent := (t.result, t.events)

theorem machine_bind_run (a : Machine α) (f : α → Machine β) (events : List HelperEvent) :
    (a >>= f).run events = (a.run events).bind (fun p => (f p.1).run p.2) := rfl

theorem machine_pure_run (a : α) (events : List HelperEvent) :
    (pure a : Machine α).run events = some (a, events) := rfl

theorem machine_lift_run (a : Option α) (events : List HelperEvent) :
    (FKS2Scalar.liftOption a).run events = a.map (fun v => (v, events)) := rfl

set_option linter.unusedSimpArgs false in
theorem traceLoop_project (fuel : Nat) (st : Frame) (name : String) (bound : Rat)
    (inclusive : Bool) (body : List Stmt) (events : List HelperEvent) :
    (traceLoop fuel st name bound inclusive body events).map project =
      (evalLoop round64 selectedAST fuel st name bound inclusive body).run events := by
  induction fuel generalizing st events with
  | zero => rfl
  | succ n ih =>
    by_cases hr : st.result.isSome = true
    · simp only [StateT.run, StateT.bind, StateT.pure, FKS2Scalar.liftOption, traceLoop, evalLoop, hr, Bool.false_eq_true, ↓reduceIte]
      rfl
    · simp only [StateT.run, StateT.bind, StateT.pure, FKS2Scalar.liftOption, traceLoop, evalLoop, hr, Bool.false_eq_true, ↓reduceIte]
      try simp only [StateT.run, StateT.bind, StateT.pure, FKS2Scalar.liftOption, machine_bind_run, machine_lift_run, machine_pure_run,
        Bool.false_eq_true, Bool.false_eq_true, ↓reduceIte, Option.bind_map, Option.map_bind, Option.map_some,
        Option.bind_some]
      cases hg : get st.env name with
      | none => simp [StateT.run, StateT.bind, StateT.pure, FKS2Scalar.liftOption, bind, pure, hg]
      | some k =>
        simp only [StateT.run, StateT.bind, StateT.pure, FKS2Scalar.liftOption, bind, pure, Option.bind_some, Option.map_some, Function.comp_apply]
        by_cases hc : (if inclusive then k ≤ bound else k < bound)
        · simp only [StateT.run, StateT.bind, StateT.pure, FKS2Scalar.liftOption, bind, pure, Function.comp_apply, hc, Bool.false_eq_true, ↓reduceIte,
            machine_bind_run, machine_lift_run, machine_pure_run,
            Option.bind_map, Option.map_bind, Option.bind_some]
          cases hb : (evalBlock round64 selectedAST n st body).run events with
          | none => simp [StateT.run, StateT.bind, StateT.pure, FKS2Scalar.liftOption, StateT.run] at hb; simp [StateT.run, StateT.bind, StateT.pure, FKS2Scalar.liftOption, hb]
          | some pair =>
            rcases pair with ⟨next, ev⟩
            simp only [StateT.run, StateT.bind, StateT.pure, FKS2Scalar.liftOption, StateT.run] at hb
            simp only [StateT.run, StateT.bind, StateT.pure, FKS2Scalar.liftOption, hb, bind, pure, Option.bind_some]
            by_cases hn : next.result.isSome = true
            · simp [StateT.run, StateT.bind, StateT.pure, FKS2Scalar.liftOption, hn, project]
            · simp only [StateT.run, StateT.bind, StateT.pure, FKS2Scalar.liftOption, hn, Bool.false_eq_true, ↓reduceIte, machine_bind_run, machine_lift_run,
                machine_pure_run, Option.bind_map, Option.map_bind]
              cases ho : get next.env name with
              | none => simp [StateT.run, StateT.bind, StateT.pure, FKS2Scalar.liftOption, bind, pure, ho]
              | some old =>
                simp only [StateT.run, StateT.bind, StateT.pure, FKS2Scalar.liftOption, bind, pure, Function.comp_apply, ho, Option.bind_some, Option.map_some]
                cases hv : round64 (old + 1) with
                | none => simp [StateT.run, StateT.bind, StateT.pure, FKS2Scalar.liftOption, bind, pure, hv]
                | some value =>
                  simp only [StateT.run, StateT.bind, StateT.pure, FKS2Scalar.liftOption, bind, pure, Function.comp_apply, hv, Option.bind_some, Option.map_some]
                  have hp := ih { next with env := put next.env name value } ev
                  cases ht : traceLoop n { next with env := put next.env name value }
                      name bound inclusive body ev with
                  | none => simpa [StateT.run, ht, project] using hp
                  | some t => simpa [StateT.run, ht, project] using hp
        · simp [StateT.run, StateT.bind, StateT.pure, FKS2Scalar.liftOption, bind, pure, Function.comp_apply, hc, machine_pure_run, project]

/-- Descriptors and prefixes are read from the selected, source-checked main AST. -/
def mainBody : List Stmt := mainFunction.body

def beforeLoops : Option (Frame × List HelperEvent) :=
  (evalBlock round64 selectedAST 1024 ⟨[], none⟩ (mainBody.take 5)).run []

def runLoop (fuel : Nat) (state : Frame) (events : List HelperEvent) (stmt : Stmt) :
    Option LoopTrace := do
  let .loop name start bound inclusive body := stmt | none
  let (x, e1) ← (evalExpr round64 selectedAST (fuel - 1) state.env start).run events
  let (y, e2) ← (evalExpr round64 selectedAST (fuel - 1) state.env bound).run e1
  traceLoop (fuel - 1) { state with env := put state.env name x } name y inclusive body e2

def trace1 : LoopTrace := (do
  let (state, events) ← beforeLoops
  let stmt ← mainBody[5]?
  runLoop 1018 state events stmt).getD ⟨⟨[], none⟩, [], []⟩

def trace2 : LoopTrace := (do
  let stmt ← mainBody[6]?
  runLoop 1017 trace1.result trace1.events stmt).getD ⟨⟨[], none⟩, [], []⟩

def eventOf (step : Iteration) : HelperEvent := step.eventsAfter.headD ⟨"", 0, 0⟩
def termOf (step : Iteration) : Rat := (eventOf step).out
def counterOf (step : Iteration) : Rat := (get step.before.env "k").getD 0

def terms1 : List Rat := trace1.steps.map termOf
def terms2 : List Rat := trace2.steps.map termOf

def acc1 : Rat := (get trace1.result.env "s1").getD 0
def acc2 : Rat := (get trace2.result.env "s2").getD 0

def fullFrame : Frame :=
  ((evalBlock round64 selectedAST 1024 ⟨[], none⟩ mainBody).run []).getD (⟨[], none⟩, []) |>.1

def initialLoops : Frame × List HelperEvent := beforeLoops.getD (⟨[], none⟩, [])
def loop1Stmt : Stmt := (mainBody[5]?).getD (.ret (.lit "0.0"))
def loop2Stmt : Stmt := (mainBody[6]?).getD (.ret (.lit "0.0"))

/-- Exact residual-fuel calls of the original evaluator, including the whole main execution. -/
def TraceConnection : Prop :=
    (do let (state, events) ← beforeLoops
        let stmt ← mainBody[5]?
        runLoop 1018 state events stmt) = some trace1 ∧
    (do let stmt ← mainBody[6]?
        runLoop 1017 trace1.result trace1.events stmt) = some trace2 ∧
    beforeLoops = some initialLoops ∧
    (evalStmt round64 selectedAST 1018 initialLoops.1 loop1Stmt).run initialLoops.2 =
      some (trace1.result, trace1.events) ∧
    (evalStmt round64 selectedAST 1017 trace1.result loop2Stmt).run trace1.events =
      some (trace2.result, trace2.events) ∧
    (evalBlock round64 selectedAST 1017 trace2.result (mainBody.drop 7)).run trace2.events =
      some (fullFrame, helperEvents.reverse) ∧
    (evalBlock round64 selectedAST 1024 ⟨[], none⟩ mainBody).run [] =
      some (fullFrame, helperEvents.reverse) ∧ fullFrame.result = some q

theorem source_trace_execution : TraceConnection := by
  unfold TraceConnection
  native_decide

end FKS2SumBridge
