/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedWinnerA.Certificate
import ScopedWinnerA.Sensitivity
open Lean WinnerProgramA

def main (args : List String) : IO UInt32 := do
  match args with
  | ["p1"] =>
    let out:=run ScopedWinnerA.Certificate.program
    let accepted:=acceptUpper out ScopedWinnerA.Certificate.bounds
    let rows:=out.map fun v=>
      let r:=v.1.toIntervalRat
      Json.mkObj [("lo",toJson (toString r.lo)),("hi",toJson (toString r.hi)),("domain",toJson v.2)]
    IO.println <| (Json.mkObj [("route",toJson "p1"),("rows",toJson rows),
      ("accepted",toJson accepted),("cells",toJson (16385:Nat))]).compress
    return if accepted then 0 else 1
  | ["sensitivity"] =>
    let rows:=ScopedWinnerA.Sensitivity.scenarios.map fun z=>
      let out:=run (WinnerBetaA.Numerical.program z.1 240)
      let accepted:=acceptUpper out [z.2]
      Json.mkObj [("beta",toJson (toString z.1)),("cap",toJson (toString z.2)),("accepted",toJson accepted),
        ("intervals",toJson (out.map fun v=>let r:=v.1.toIntervalRat;
          Json.mkObj [("lo",toJson (toString r.lo)),("hi",toJson (toString r.hi)),("domain",toJson v.2)]))]
    IO.println <| (Json.mkObj [("route",toJson "sensitivity"),("rows",toJson rows),
      ("accepted",toJson ScopedWinnerA.Sensitivity.accepted)]).compress
    return if ScopedWinnerA.Sensitivity.accepted then 0 else 1
  | _ => IO.eprintln "usage: scoped-winner p1|sensitivity"; return 2
