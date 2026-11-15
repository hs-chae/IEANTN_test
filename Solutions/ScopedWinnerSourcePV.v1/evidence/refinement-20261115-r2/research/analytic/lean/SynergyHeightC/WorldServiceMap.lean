/- Sound extension of source-verified world callbacks. No new source rule or
execution success is introduced; every successful old callback is preserved. -/
import ScopedIO.WorldSource
namespace SynergyHeightC.WorldServiceMap
open ScopedC ScopedC.Syntax ScopedC.Machine ScopedIO
set_option autoImplicit false
set_option maxHeartbeats 20000
set_option maxRecDepth 100000

def Included (old fresh : WorldIO.Call) : Prop :=
  ∀ name args s v t, old name args s=some (v,t) → fresh name args s=some (v,t)

theorem evaluation {cfg : Layout} {pure : Machine.Call} {old fresh : WorldIO.Call}
    {platform : WorldIO.Platform} (included : Included old fresh)
    {e : Expr} {s t : WorldIO.World} {v : Value}
    (run : WorldSource.Eval cfg pure old platform e s t v) :
    WorldSource.Eval cfg pure fresh platform e s t v := by
  induction run using WorldSource.Eval.rec
    (motive_2:=fun es s t vs _=>WorldSource.Arguments cfg pure fresh platform es s t vs) with
  | pure h => exact .pure h
  | stdout h => exact .stdout h
  | call args accepted ih => exact .call ih (included _ _ _ _ _ accepted)
  | binary ordinary left right arithmetic ihLeft ihRight =>
      exact .binary ordinary ihLeft ihRight arithmetic
  | nil s => exact .nil s
  | cons first rest ihFirst ihRest => exact .cons ihFirst ihRest

theorem arguments {cfg : Layout} {pure : Machine.Call} {old fresh : WorldIO.Call}
    {platform : WorldIO.Platform} (included : Included old fresh)
    {es : List Expr} {s t : WorldIO.World} {vs : List Value}
    (run : WorldSource.Arguments cfg pure old platform es s t vs) :
    WorldSource.Arguments cfg pure fresh platform es s t vs := by
  induction run using WorldSource.Arguments.rec
    (motive_1:=fun e s t v _=>WorldSource.Eval cfg pure fresh platform e s t v) with
  | pure h => exact .pure h
  | stdout h => exact .stdout h
  | call args accepted ih => exact .call ih (included _ _ _ _ _ accepted)
  | binary ordinary left right arithmetic ihLeft ihRight =>
      exact .binary ordinary ihLeft ihRight arithmetic
  | nil s => exact .nil s
  | cons first rest ihFirst ihRest => exact .cons ihFirst ihRest

theorem guard {cfg : Layout} {pure : Machine.Call} {old fresh : WorldIO.Call}
    {platform : WorldIO.Platform} (included : Included old fresh)
    {e : Option Expr} {s t : WorldIO.World} {b : Bool}
    (run : Loops.GuardRun (WorldSource.Eval cfg pure old platform) truth e s t b) :
    Loops.GuardRun (WorldSource.Eval cfg pure fresh platform) truth e s t b := by
  cases run with
  | omitted s => exact .omitted s
  | present test => exact .present (evaluation included test)

theorem statement {cfg : Layout} {pure : Machine.Call} {old fresh : WorldIO.Call}
    {platform : WorldIO.Platform} (included : Included old fresh)
    {st : Stmt} {s : WorldIO.World} {out : Loops.Flow WorldIO.World Value}
    (run : WorldSource.Run cfg pure old platform st s out) :
    WorldSource.Run cfg pure fresh platform st s out :=
  Loops.StmtRun.rec
    (motive_1:=fun st s out _=>WorldSource.Run cfg pure fresh platform st s out)
    (motive_2:=fun ss s out _=>Loops.SeqRun
      (WorldSource.Eval cfg pure fresh platform) (WorldSource.Declare cfg pure)
      truth WorldSource.Scope ss s out)
    (motive_3:=fun cond step body s out _=>Loops.ForRun
      (WorldSource.Eval cfg pure fresh platform) (WorldSource.Declare cfg pure)
      truth WorldSource.Scope cond step body s out)
    (motive_4:=fun cond body s out _=>Loops.WhileRun
      (WorldSource.Eval cfg pure fresh platform) (WorldSource.Declare cfg pure)
      truth WorldSource.Scope cond body s out)
    (fun s=>.skip s)
    (fun h=>.evaluate (evaluation included h))
    (fun h=>.declare h)
    (fun h=>.returnValue (evaluation included h))
    (fun test _ ih=>.branch (evaluation included test) ih)
    (fun _ scope ih=>.sequence ih scope)
    (fun _ _ scope ihInit ihLoop=>.forLoop ihInit ihLoop scope)
    (fun _ scope ih=>.forInitialReturn ih scope)
    (fun _ ih=>.whileLoop ih)
    (fun s=>.nil s)
    (fun _ _ ihFirst ihRest=>.next ihFirst ihRest)
    (fun _ ih=>.returned ih)
    (fun test=>.done (guard included test))
    (fun test _ increment _ ihBody ihRest=>.next (guard included test) ihBody
      (evaluation included increment) ihRest)
    (fun test _ ih=>.returned (guard included test) ih)
    (fun test stop=>.done (evaluation included test) stop)
    (fun test keepGoing _ _ ihBody ihRest=>.next (evaluation included test) keepGoing ihBody ihRest)
    (fun test keepGoing _ ih=>.returned (evaluation included test) keepGoing ih)
    run

#print axioms evaluation
#print axioms arguments
#print axioms statement
end SynergyHeightC.WorldServiceMap
