/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedC.IntervalCasts
import ScopedC.DeclarationReturn
import ScopedC.LocalScope
import ScopedC.OneFrames

namespace ScopedC.RationalPointCalls
open ScopedC.Syntax ScopedC.Machine ScopedC.SourceCalls
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def frame (s : State) (q : Value) : State := OneFrames.frame s "Q" "q" q

def initializer : Expr := .record [.var "q",.var "q"]

theorem point_closed (code : List Function) (installed : Generated.f_point∈code)
    {s : State} {mag n neg den d : Nat}
    (magLive : NatArena.Borrow s.nats mag n) (denLive : NatArena.Borrow s.nats den d)
    (bound : neg<2^32) :
    SourceCall Header.layout code 1 "point" [RecordCasts.rational mag neg den] s
      (IntervalCasts.value (RecordCasts.rational mag neg den) (RecordCasts.rational mag neg den)) s := by
  let q := RecordCasts.rational mag neg den
  let result := IntervalCasts.value q q
  let service : Call := fun _ _ _ => none
  have initializedQ : Machine.initialized 1000 q=true := by rfl
  have initializedRI : Machine.initialized 1000 result=true := by rfl
  have var : evalExpr Header.layout service 999 (frame s q) (.var "q")=some (q,frame s q) :=
    TypedFrames.allocate_eval Header.layout service 998 {s with env:=[]}
      "Q" "q" q initializedQ (by decide) (by decide) (by decide) (by decide)
  have expr : evalExpr Header.layout service 1000 (frame s q) initializer=
      some (.aggregate [q,q],frame s q) :=
    ExpressionTemplates.record_two Header.layout service var var
  have child : castValue Header.layout (frame s q) 99 "Q" q=some q :=
    RecordCasts.rational_record (frame s q) 96 "Q" (by decide +kernel) magLive denLive bound
  have cast : castValue Header.layout (frame s q) 100 "RI" (.aggregate [q,q])=some result :=
    IntervalCasts.aggregate (frame s q) 96 q q child child
  have body := DeclarationReturn.body Header.layout service "RI" "r" initializer expr cast initializedRI
    (by decide) (by decide) (by decide) (by decide)
  rw [LocalScope.pop_local "RI" "r" result (s:=frame s q) (t:=frame s q) rfl rfl] at body
  apply installed_body (f:=Generated.f_point) (rank:=0) installed
    (fun _ _ _ _ _ h => by cases h)
    (TypedFrames.bind_one Header.layout s "Q" "q" q q
      (RecordCasts.rational_record {s with env:=[]} 97 "Q" (by decide +kernel) magLive denLive bound)) body
  exact ⟨IntervalCasts.record (frame s q) 96 "static RI" (by decide +kernel) q q child child,
    (OneFrames.pop_frame "Q" "q" q rfl rfl).symm⟩

end ScopedC.RationalPointCalls
