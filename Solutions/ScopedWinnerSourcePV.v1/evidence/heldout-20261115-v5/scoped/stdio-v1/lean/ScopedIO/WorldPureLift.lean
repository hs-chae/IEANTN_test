/- Successful existing pure C statement trees lift into the separate stdio
world without changing the stream. This is a theorem about the existing
semantics, not a new application execution or success primitive. -/
import ScopedIO.WorldSourceWith

namespace ScopedIO.WorldPureLift
open ScopedC ScopedC.Syntax ScopedC.Machine ScopedIO.WorldIO
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 100000

def flow (stream : Stream) : Loops.Flow State Value → Loops.Flow World Value
  | .continuing s => .continuing ⟨s,stream⟩
  | .returned s v => .returned ⟨s,stream⟩ v

theorem eval {cfg : Layout} {service : Machine.Call} {external : WorldIO.Call}
    {platform : Platform} {e : Expr} {s t : State} {v : Value}
    (old : SourceCalls.Eval cfg service e s t v) (stream : Stream) :
    WorldSource.Eval cfg service external platform e ⟨s,stream⟩ ⟨t,stream⟩ v := by
  obtain ⟨fuel,run⟩ := old
  exact WorldSource.Eval.pure run

theorem declare {cfg : Layout} {service : Machine.Call} {ds : List Decl} {s t : State}
    (old : SourceCalls.Declare cfg service ds s t) (stream : Stream) :
    WorldSource.Declare cfg service ds ⟨s,stream⟩ ⟨t,stream⟩ :=
  ⟨ArrayLegacyLift.declarations_success old,rfl⟩

theorem scope {s : State} {inner outer : Loops.Flow State Value}
    (old : SourceCalls.Scope s inner outer) (stream : Stream) :
    WorldSource.Scope ⟨s,stream⟩ (flow stream inner) (flow stream outer) := by
  cases inner <;> cases outer <;>
    simpa [SourceCalls.Scope,WorldSource.Scope,WorldSource.pop,flow] using old

theorem guard {cfg : Layout} {service : Machine.Call} {external : WorldIO.Call}
    {platform : Platform} {cond : Option Expr} {s t : State} {value : Bool}
    (old : Loops.GuardRun (SourceCalls.Eval cfg service) truth cond s t value)
    (stream : Stream) :
    Loops.GuardRun (WorldSource.Eval cfg service external platform) truth cond
      ⟨s,stream⟩ ⟨t,stream⟩ value := by
  cases old with
  | omitted s => exact Loops.GuardRun.omitted _
  | present run => exact Loops.GuardRun.present (eval run stream)

theorem statement {cfg : Layout} {service : Machine.Call} {external : WorldIO.Call}
    {platform : Platform} {st : Stmt} {s : State} {out : Loops.Flow State Value}
    (old : SourceCalls.Run cfg service st s out) (stream : Stream) :
    WorldSource.Run cfg service external platform st ⟨s,stream⟩ (flow stream out) := by
  exact Loops.StmtRun.rec
    (motive_1:=fun st s out _=>∀ stream,WorldSource.Run cfg service external platform st
      ⟨s,stream⟩ (flow stream out))
    (motive_2:=fun ss s out _=>∀ stream,Loops.SeqRun
      (WorldSource.Eval cfg service external platform) (WorldSource.Declare cfg service)
      truth WorldSource.Scope ss ⟨s,stream⟩ (flow stream out))
    (motive_3:=fun cond step body s out _=>∀ stream,Loops.ForRun
      (WorldSource.Eval cfg service external platform) (WorldSource.Declare cfg service)
      truth WorldSource.Scope cond step body ⟨s,stream⟩ (flow stream out))
    (motive_4:=fun cond body s out _=>∀ stream,Loops.WhileRun
      (WorldSource.Eval cfg service external platform) (WorldSource.Declare cfg service)
      truth WorldSource.Scope cond body ⟨s,stream⟩ (flow stream out))
    (fun s stream=>Loops.StmtRun.skip _)
    (fun run stream=>Loops.StmtRun.evaluate (eval run stream))
    (fun run stream=>Loops.StmtRun.declare (declare run stream))
    (fun run stream=>Loops.StmtRun.returnValue (eval run stream))
    (fun test _ mapped stream=>Loops.StmtRun.branch (eval test stream) (mapped stream))
    (fun _ exit mapped stream=>Loops.StmtRun.sequence (mapped stream) (scope exit stream))
    (fun _ _ exit initial loop stream=>Loops.StmtRun.forLoop
      (initial stream) (loop stream) (scope exit stream))
    (fun _ exit initial stream=>Loops.StmtRun.forInitialReturn (initial stream) (scope exit stream))
    (fun _ mapped stream=>Loops.StmtRun.whileLoop (mapped stream))
    (fun s stream=>Loops.SeqRun.nil _)
    (fun _ _ first rest stream=>Loops.SeqRun.next (first stream) (rest stream))
    (fun _ mapped stream=>Loops.SeqRun.returned (mapped stream))
    (fun test stream=>Loops.ForRun.done (guard test stream))
    (fun test _ step _ iteration rest stream=>Loops.ForRun.next
      (guard test stream) (iteration stream) (eval step stream) (rest stream))
    (fun test _ iteration stream=>Loops.ForRun.returned (guard test stream) (iteration stream))
    (fun test stop stream=>Loops.WhileRun.done (eval test stream) stop)
    (fun test keep _ _ iteration rest stream=>Loops.WhileRun.next
      (eval test stream) keep (iteration stream) (rest stream))
    (fun test keep _ iteration stream=>Loops.WhileRun.returned
      (eval test stream) keep (iteration stream))
    old stream

theorem while_run {cfg : Layout} {service : Machine.Call} {external : WorldIO.Call}
    {platform : Platform} {cond : Expr} {body : Stmt} {s : State} {out : Loops.Flow State Value}
    (old : Loops.WhileRun (SourceCalls.Eval cfg service) (SourceCalls.Declare cfg service)
      truth SourceCalls.Scope cond body s out) (stream : Stream) :
    Loops.WhileRun (WorldSource.Eval cfg service external platform)
      (WorldSource.Declare cfg service) truth WorldSource.Scope cond body
      ⟨s,stream⟩ (flow stream out) := by
  have lifted := statement (external:=external) (platform:=platform)
    (Loops.StmtRun.whileLoop old) stream
  cases lifted with
  | whileLoop run => exact run

end ScopedIO.WorldPureLift
